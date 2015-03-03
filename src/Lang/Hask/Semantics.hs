module Lang.Hask.Semantics where

import FP hiding (Kon, konI, konE)

import Lang.Hask.CPS
import Name
import Literal
import DataCon
import CoreSyn (AltCon(..))

type Env τ = Map Name (Addr τ)
type Store ν τ = Map (Addr τ) (ν τ)

data Addr τ = Addr
  { addrName :: Name
  , addrLexTime :: τ
  , addrDynTime :: τ
  }

data PicoVal τ =
    AddrVal (Addr τ)
  | LitVal Literal

data CloF τ = CloF
  { cloFLamArg :: Name
  , cloFKonArg :: Name
  , cloFBody :: Call
  , cloFEnv :: Env τ
  , cloFTime :: τ
  }

data CloK τ = CloK
  { cloKArg :: Name
  , cloKBody :: Call
  , cloKEnv :: Env τ
  }

data CaseK τ = CaseK
  { caseKBranches :: [CaseBranch]
  , caseKBody :: Call
  , caseKEnv :: Env τ
  }

data AppToK τ = AppToK
  { appToKArg :: Pico
  , appToKKon :: Pico
  , appToKEnv :: Env τ
  , appToKTime :: τ
  }

data Kon τ =
    CloKon (CloK τ)
  | CaseKon (CaseK τ)
  | AppToKon (AppToK τ)
makePrisms ''Kon

data Data τ = Data
  { dataCon :: DataCon
  , dataArgs :: [PicoVal τ]
  }

data Thunk τ = Thunk
  { thunkName :: Name
  , thunkFun :: Pico
  , thunkArg :: Pico
  , thunkEnv :: Env τ
  , thunkTime :: τ
  }

class Val ν τ where
  litI :: Literal -> ν τ
  litTestE :: Literal -> ν τ -> Set Bool
  dataI :: Data τ -> ν τ
  dataE :: ν τ -> Maybe (Set (Data τ))
  cloFI :: CloF τ -> ν τ
  cloFE :: ν τ -> Maybe (Set (CloF τ))
  konI :: Kon τ -> ν τ
  konE :: ν τ -> Maybe (Set (Kon τ))
  thunkI :: Thunk τ -> ν τ
  thunkE :: ν τ -> Maybe (Set (Thunk τ))
  botI :: ν τ

class Time τ where
  tzero :: τ
  tick :: Call -> τ -> τ

data 𝒮 ν τ = 𝒮
  { 𝓈Env :: Env τ
  , 𝓈Store :: Store ν τ
  , 𝓈LexTime :: τ
  , 𝓈DynTime :: τ
  }
makeLenses ''𝒮

class
  ( Monad m
  , MonadStateE (𝒮 ν τ) m
  , MonadZero m
  , MonadTop m
  , MonadPlus m
  , Val ν τ
  , Ord (Addr τ)
  , JoinLattice (ν τ)
  , Time τ
  ) => Analysis ν τ m | m -> ν , m -> τ where

tickLex :: (Analysis ν τ m) => Call -> m ()
tickLex = modifyL 𝓈LexTimeL . tick

tickDyn :: (Analysis ν τ m) => Call -> m ()
tickDyn = modifyL 𝓈DynTimeL . tick

addr :: (Analysis ν τ m) => Name -> m (Addr τ)
addr x = do
  lτ <- getL 𝓈LexTimeL
  dτ <- getL 𝓈DynTimeL
  return $ Addr x lτ dτ

bindJoin :: (Analysis ν τ m) => Name -> ν τ -> m ()
bindJoin x v = do
  𝓁 <- addr x
  modifyL 𝓈EnvL (mapInsert x 𝓁)
  modifyL 𝓈StoreL (mapInsertWith (\/) 𝓁 v)

bindSet :: (Analysis ν τ m) => Name -> ν τ -> m ()
bindSet x v = do
  𝓁 <- addr x
  modifyL 𝓈EnvL (mapInsert x 𝓁)
  modifyL 𝓈StoreL (mapInsert 𝓁 v)


var :: (Analysis ν τ m) => Name -> m (ν τ)
var x = do
  ρ <- getL 𝓈EnvL
  σ <- getL 𝓈StoreL
  liftMaybeZero $ index σ *$ index ρ $ x

pico :: (Analysis ν τ m) => Pico -> m (ν τ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

picoVal :: (Analysis ν τ m) => Pico -> m (PicoVal τ)
picoVal (Var x) = AddrVal ^$ addr x
picoVal (Lit l) = return $ LitVal l

unPicoVal :: (Analysis ν τ m) => PicoVal τ -> m (ν τ)
unPicoVal (AddrVal 𝓁) = do
  σ <- getL 𝓈StoreL
  liftMaybeZero $ index σ 𝓁
unPicoVal (LitVal l) = return $ litI l

atom :: (Analysis ν τ m) => Atom -> m (ν τ)
atom = \ case
  Pico p -> pico p
  LamF x k c -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL 𝓈LexTimeL
    return $ cloFI $ CloF x k c ρ lτ
  LamK x c -> do
    ρ <- getL 𝓈EnvL
    return $ konI $ CloKon $ CloK x c ρ

refinePico :: (Analysis ν τ m) => Pico -> ν τ -> m ()
refinePico (Var x) v = do
  𝓁 <- addr x
  modifyL 𝓈StoreL (mapInsert 𝓁 v)
refinePico (Lit _) _ = return ()

call :: (Analysis ν τ m) => Call -> m Call
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
      v₃ <- pico p₃
      kon <- elimMaybe mtop mset $ konE v₃
      refinePico p₃ $ konI kon
      case kon of
        -- The continuation is a source continuation. Don't even look at f or
        -- x, put them in a thunk and continue.
        CloKon (CloK x c' ρ') -> do
          ρ <- getL 𝓈EnvL
          lτ <- getL 𝓈LexTimeL
          putL 𝓈EnvL ρ'
          bindJoin x $ thunkI $ Thunk undefined p₁ p₂ ρ lτ
          return c'
        -- The continuation is a case expression context.
        -- 1. If the function is a lambda, call it and continue to the case
        --    continuation.
        -- 2. If the function is a thunk, start applying the thunk and add a
        --    continuation to the stack.
        CaseKon _ -> do
          v₁ <- pico p₁
          msum
            [ do
                f@(CloF x k c' ρ' lτ') <- elimMaybe mtop mset $ cloFE v₁
                refinePico p₁ $ cloFI f
                v₂ <- pico p₂
                putL 𝓈EnvL ρ'
                putL 𝓈LexTimeL lτ'
                bindJoin x v₂
                bindJoin k $ konI kon
                return c'
            , do
                f@(Thunk k p₁' p₂' ρ' lτ') <- elimMaybe mtop mset $ thunkE v₁
                refinePico p₁ $ thunkI f
                ρ <- getL 𝓈EnvL
                lτ <- getL 𝓈LexTimeL
                putL 𝓈EnvL ρ'
                putL 𝓈LexTimeL lτ'
                bindJoin k $ konI $ AppToKon $ AppToK p₂ (Var k) ρ lτ
                return $ Fix $ AppF p₁' p₂' (Var k)
            ]
        -- The continuation is a function application context.
        -- 1. If the function is a lambda, call it and continue to the function
        --    application.
        -- 2. If the function is a thunk, start applying the thunk and add a
        --    continuation to the stack.
        AppToKon (AppToK p₁' p₂' ρ' lτ') -> do
          v₁ <- pico p₁
          msum
            [ do
                f@(CloF x k c' ρ'' lτ'') <- elimMaybe mtop mset $ cloFE v₁
                refinePico p₁ $ cloFI f
                v₂ <- pico p₂
                putL 𝓈EnvL ρ'
                -- LOH
                undefined
            , do
                f@(Thunk k p₁' p₂' ρ' lτ') <- elimMaybe mtop mset $ thunkE v₁
                refinePico p₁ $ thunkI f
                undefined
            ]
    AppK p₁ p₂ -> do
      v₁ <- pico p₁
      v₂ <- pico p₂
      k@(CloK x c' ρ) <- liftMaybeZero . coerce cloKonL *$ elimMaybe mtop mset $ konE v₁
      refinePico p₁ $ konI $ CloKon k
      putL 𝓈EnvL ρ
      bindJoin x v₂
      return c'
    Case p bs -> do
      v <- pico p
      msum 
        [ do
            msum $ mapOn bs $ \ (CaseBranch acon xs c') -> do
              case acon of
                DataAlt con -> do
                  d@(Data vcon pvs) <- elimMaybe mtop mset $ dataE v 
                  refinePico p $ dataI d
                  guard $ con == vcon
                  xpvs <- liftMaybeZero $ zip xs pvs
                  traverseOn xpvs $ \ (x, pv) -> do
                    𝓁 <- addr x
                    v' <- unPicoVal pv 
                    modifyL 𝓈StoreL $ mapInsert 𝓁 v'
                  return c'
                LitAlt l -> do
                  guard *$ mset $ litTestE l v
                  refinePico p $ litI l
                  return c'
                DEFAULT -> return c'
        , do
            t@(Thunk k pv₁ pv₂ ρ lτ) <- elimMaybe mtop mset $ thunkE v
            refinePico p $ thunkI t
            putL 𝓈EnvL ρ
            putL 𝓈LexTimeL lτ
            undefined
            -- return $ ApplyCase pv₁ pv₂ p bs
        ]
