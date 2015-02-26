module Lang.Hask.Semantics where

import FP

import Lang.Hask.CPS
import Name
import Literal
import DataCon
import CoreSyn (AltCon(..))

type Env τ = Map Name (Addr τ)
type Store δ τ = Map (Addr τ) (δ τ)

data Addr τ = Addr
  { addrName :: Name
  , addrLexTime :: τ
  , addrDynTime :: τ
  }

data CloF τ = CloF
  { cloFLamArg :: Name
  , cloFKonArg :: Name
  , cloFBody :: Call
  , cloFEnv :: Env τ
  , cloFTime :: τ
  }

data CloK τ = CloK
  { cloKLamArg :: Name
  , cloKBody :: Call
  , cloKEnv :: Env τ
  }

data Data τ = Data
  { dataCon :: DataCon
  , dataArgs :: [Addr τ]
  }

data Val τ = 
    LitV Literal
  | CloFV (CloF τ)
  | CloKV (CloK τ)
  | BotV

class Domain δ τ where
  litI :: Literal -> δ τ
  litTestE :: Literal -> δ τ -> Set Bool
  dataI :: Data τ -> δ τ
  dataE :: δ τ -> Maybe (Set (Data τ))
  cloFI :: CloF τ -> δ τ
  cloFE :: δ τ -> Maybe (Set (CloF τ))
  cloKI :: CloK τ -> δ τ
  cloKE :: δ τ -> Maybe (Set (CloK τ))
  botI :: δ τ

class Time τ where
  tzero :: τ
  tick :: Call -> τ -> τ

data 𝒮 δ τ = 𝒮
  { 𝓈Env :: Env τ
  , 𝓈Store :: Store δ τ
  , 𝓈LexTime :: τ
  , 𝓈DynTime :: τ
  }
makeLenses ''𝒮

class
  ( Monad m
  , MonadStateE (𝒮 δ τ) m
  , MonadZero m
  , MonadTop m
  , MonadPlus m
  , Domain δ τ
  , Ord (Addr τ)
  , JoinLattice (δ τ)
  , Time τ
  ) => Analysis δ τ m | m -> δ , m -> τ where

tickLex :: (Analysis δ τ m) => Call -> m ()
tickLex = modifyL 𝓈LexTimeL . tick

tickDyn :: (Analysis δ τ m) => Call -> m ()
tickDyn = modifyL 𝓈DynTimeL . tick

addr :: (Analysis δ τ m) => Name -> m (Addr τ)
addr x = do
  lτ <- getL 𝓈LexTimeL
  dτ <- getL 𝓈DynTimeL
  return $ Addr x lτ dτ

bindJoin :: (Analysis δ τ m) => Name -> δ τ -> m ()
bindJoin x v = do
  𝓁 <- addr x
  modifyL 𝓈EnvL (mapInsert x 𝓁)
  modifyL 𝓈StoreL (mapInsertWith (\/) 𝓁 v)

bindSet :: (Analysis δ τ m) => Name -> δ τ -> m ()
bindSet x v = do
  𝓁 <- addr x
  modifyL 𝓈EnvL (mapInsert x 𝓁)
  modifyL 𝓈StoreL (mapInsert 𝓁 v)


var :: (Analysis δ τ m) => Name -> m (δ τ)
var x = do
  ρ <- getL 𝓈EnvL
  σ <- getL 𝓈StoreL
  liftMaybeZero $ index σ *$ index ρ $ x

pico :: (Analysis δ τ m) => Pico -> m (δ τ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

atom :: (Analysis δ τ m) => Atom -> m (δ τ)
atom = \ case
  Pico p -> pico p
  LamF x k c -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL 𝓈LexTimeL
    return $ cloFI $ CloF x k c ρ lτ
  LamK x c -> do
    ρ <- getL 𝓈EnvL
    return $ cloKI $ CloK x c ρ

refinePico :: (Analysis δ τ m) => Pico -> δ τ -> m ()
refinePico (Var x) v = do
  𝓁 <- addr x
  modifyL 𝓈StoreL (mapInsert 𝓁 v)
refinePico (Lit _) _ = return ()

call :: (Analysis δ τ m) => Call -> m Call
call c = do
  tickDyn c
  case runFix c of
    Let x a c' -> do
      v <- atom a  
      bindJoin x v
      return c'
    Rec xs c' -> do
      traverseOn xs $ \ x ->
        bindSet x botI
      return c'
    Letrec xas c' -> do
      xvs <- mapOnM xas $ \ (x, a) -> do
        v <- atom a
        return (x, v)
      traverseOn xvs $ \ (x, v) -> do
        bindSet x v
      return c'
    AppF p₁ p₂ p₃ -> do
      v₁ <- pico p₁
      v₂ <- pico p₂
      v₃ <- pico p₃
      f@(CloF x k c' ρ lτ) <- elimMaybe mtop mset $ cloFE v₁
      refinePico p₁ $ cloFI f
      putL 𝓈EnvL ρ
      bindJoin x v₂
      bindJoin k v₃
      putL 𝓈LexTimeL lτ
      tickLex c'
      return c'
    AppK p₁ p₂ -> do
      v₁ <- pico p₁
      v₂ <- pico p₂
      k@(CloK x c' ρ) <- elimMaybe mtop mset $ cloKE v₁
      refinePico p₁ $ cloKI k
      putL 𝓈EnvL ρ
      bindJoin x v₂
      return c'
    Case p aconxscs -> do
      v <- pico p
      msum $ mapOn aconxscs $ \ (acon, xs, c') -> do
        case acon of
          DataAlt con -> do
            d@(Data vcon 𝓁s) <- elimMaybe mtop mset $ dataE v 
            refinePico p $ dataI d
            guard (con == vcon)
            x𝓁s <- liftMaybeZero $ zip xs 𝓁s
            traverseOn x𝓁s $ \ (x, 𝓁) ->
              modifyL 𝓈EnvL $ mapInsert x 𝓁
            return c'
          LitAlt l -> do
            guard *$ mset $ litTestE l v
            refinePico p $ litI l
            return c'
          DEFAULT -> return c'
