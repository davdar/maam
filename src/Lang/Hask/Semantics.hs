module Lang.Hask.Semantics where

import FP

import Lang.Hask.CPS hiding (atom)
import Name
import Literal
import DataCon
import qualified CoreSyn as H

class Time τ where
  tzero :: τ
  tick :: Call -> τ -> τ

type Env τ = Map Name (Addr τ)
type Store ν τ = Map (Addr τ) (ν τ)

data Addr τ = Addr
  { addrName :: Name
  , addrLexTime :: τ
  , addrDynTime :: τ
  }

data Data τ = Data
  { dataCon :: DataCon
  , dataArgs :: [Addr τ]
  }

data FunClo τ = FunClo
  { funCloLamArg :: Name
  , funCloKonArg :: Name
  , funCloBody :: Call
  , funCloEnv :: Env τ
  , funCloTime :: τ
  }

data KonClo τ = KonClo
  { konCloArg :: Name
  , konCloBody :: Call
  , konCloEnv :: Env τ
  }

data ThunkClo τ = ThunkClo
  { thunkCloArgName :: Name
  , thunkCloKonName :: Name
  , thunkCloFun :: Pico
  , thunkCloArg :: Pico
  , thunkCloEnv :: Env τ
  , thunkCloTime :: τ
  }

data DelayVal τ = DelayVal
  { delayValAddr :: Addr τ
  , delayValName :: Name
  }

class Val ν τ where
  litI :: Literal -> ν τ
  negLitI :: Literal -> ν τ
  litTestE :: Literal -> ν τ -> Set Bool
  dataI :: Data τ -> ν τ
  negDataI :: DataCon -> ν τ
  dataE :: ν τ -> Maybe (Set (Data τ))
  konCloI :: KonClo τ -> ν τ
  konCloE :: ν τ -> Maybe (Set (KonClo τ))
  funCloI :: FunClo τ -> ν τ
  funCloE :: ν τ -> Maybe (Set (FunClo τ))
  thunkCloI :: ThunkClo τ -> ν τ
  thunkCloE :: ν τ -> Maybe (Set (ThunkClo τ))
  delayI :: DelayVal τ -> ν τ
  delayE :: ν τ -> Maybe (Set (DelayVal τ))
  forcedI :: ν τ
  testForcedE :: ν τ -> Set Bool

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
  , MeetLattice (ν τ)
  , Time τ
  ) => Analysis ν τ m | m -> ν , m -> τ where

-- Finite observations on values in the abstract domain

refinePico :: (Analysis ν τ m) => Pico -> ν τ -> m ()
refinePico (Var x) v = do
  𝓁 <- alloc x
  modifyL 𝓈StoreL $ mapInsertWith (/\) 𝓁 v
refinePico (Lit _) _ = return ()

extract :: (Analysis ν τ m) => (a -> ν τ) -> (ν τ -> Maybe (Set a)) -> Pico -> ν τ -> m a
extract intro elim p v = do
  a <- elimMaybe mtop mset $ elim v
  refinePico p $ intro a
  return a

extractIsLit :: (Analysis ν τ m) => Literal -> Pico -> ν τ -> m ()
extractIsLit l p v = do
  b <- mset $ litTestE l v
  guard b
  refinePico p $ litI l

-- Time management

tickLex :: (Analysis ν τ m) => Call -> m ()
tickLex = modifyL 𝓈LexTimeL . tick

tickDyn :: (Analysis ν τ m) => Call -> m ()
tickDyn = modifyL 𝓈DynTimeL . tick

alloc :: (Analysis ν τ m) => Name -> m (Addr τ)
alloc x = do
  lτ <- getL 𝓈LexTimeL
  dτ <- getL 𝓈DynTimeL
  return $ Addr x lτ dτ

-- Updating values in the store

bindJoin :: (Analysis ν τ m) => Name -> ν τ -> m ()
bindJoin x v = do
  𝓁 <- alloc x
  modifyL 𝓈EnvL $ mapInsert x 𝓁
  modifyL 𝓈StoreL $ mapInsertWith (\/) 𝓁 v

bindSet :: (Analysis ν τ m) => Name -> ν τ -> m ()
bindSet x v = do
  𝓁 <- alloc x
  modifyL 𝓈EnvL (mapInsert x 𝓁)
  modifyL 𝓈StoreL (mapInsert 𝓁 v)

-- Denotations

addr :: (Analysis ν τ m) => Addr τ -> m (ν τ)
addr 𝓁 = do
  σ <- getL 𝓈StoreL
  liftMaybeZero $ σ # 𝓁

var :: (Analysis ν τ m) => Name -> m (ν τ)
var x = do
  ρ <- getL 𝓈EnvL
  addr *$ liftMaybeZero $ ρ # x

pico :: (Analysis ν τ m) => Pico -> m (ν τ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

atom :: (Analysis ν τ m) => Atom -> m (ν τ)
atom = \ case
  Pico p -> pico p
  LamF x k c -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL 𝓈LexTimeL
    return $ funCloI $ FunClo x k c ρ lτ
  LamK x c -> do
    ρ <- getL 𝓈EnvL
    return $ konCloI $ KonClo x c ρ
  Thunk x k p₁ p₂ -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL 𝓈LexTimeL
    return $ thunkCloI $ ThunkClo x k p₁ p₂ ρ lτ

forceThunk :: (Analysis ν τ m) => Pico -> (Pico -> Call) -> m Call
forceThunk p mk = do
  v <- pico p
  msum
    [ do
        ThunkClo x k p₁' p₂' ρ lτ <- extract thunkCloI thunkCloE p v
        putL 𝓈EnvL ρ
        putL 𝓈LexTimeL lτ
        kv <- atom $ LamK x $ mk $ Var x
        bindJoin k kv
        return $ Fix $ AppF p₁' p₂' $ Var k
    , do
        DelayVal 𝓁 x <- extract delayI delayE p v
        v' <- addr 𝓁
        bindJoin x v'
        return $ mk $ Var x
    ]

call :: (Analysis ν τ m) => Call -> m Call
call c = do
  tickDyn c
  case runFix c of
    Let x a c' -> do
      v <- atom a  
      bindJoin x v
      return c'
    Rec xxs c' -> do
      traverseOn xxs $ \ (x,x') -> do
        𝓁 <- alloc x
        bindSet x . delayI $ DelayVal 𝓁 x'
      return c'
    Letrec xas c' -> do
      traverseOn xas $ \ (x, a) -> do
        bindSet x *$ atom a
      return c'
    AppK p₁ p₂ -> do
      v₁ <- pico p₁
      v₂ <- pico p₂
      KonClo x c' ρ <- extract konCloI konCloE p₁ v₁
      putL 𝓈EnvL ρ
      bindJoin x v₂
      return c'
    AppF p₁ p₂ p₃ -> msum
      [ do
          v₁ <- pico p₁
          FunClo x k c' ρ lτ <- extract funCloI funCloE p₁ v₁
          v₂ <- pico p₂
          v₃ <- pico p₃
          putL 𝓈EnvL ρ
          putL 𝓈LexTimeL lτ
          bindJoin x v₂
          bindJoin k v₃
          return c'
      , forceThunk p₁ $ \ p -> Fix $ AppF p p₂ p₃
      ]
    Case p bs0 -> msum
      [ do
          v <- pico p  
          -- loop through the alternatives
          let loop bs = do
                (CaseBranch acon xs c', bs') <- liftMaybeZero $ coerce consL bs
                case acon of
                  H.DataAlt con -> msum
                    -- The alt is a Data and the value is a Data with the same
                    -- tag; jump to the alt body.
                    [ do
                        Data dcon 𝓁s <- extract dataI dataE p v
                        guard $ con == dcon
                        x𝓁s <- liftMaybeZero $ zip xs 𝓁s
                        traverseOn x𝓁s $ \ (x, 𝓁) -> do
                          v' <- addr 𝓁
                          bindJoin x v'
                        return c'
                    -- The alt is a Data and the value is not a Data with the
                    -- same tag; try the next branch.
                    , do
                        refinePico p $ negDataI con
                        loop bs'
                    ]
                  H.LitAlt l -> msum
                    -- The alt is a Lit and the value is the same lit; jump to
                    -- the alt body.
                    [ do
                        extractIsLit l p v
                        return c'
                    -- The alt is a Lit and and the value is not the same lit;
                    -- try the next branch.
                    , do
                        refinePico p $ negLitI l
                        loop bs'
                    ]
                  -- The alt is the default branch; jump to the body _only if
                  -- the value is forced_ (i.e. not a thunk or delay).
                  H.DEFAULT -> do
                    f <- mset $ testForcedE v
                    guard f
                    refinePico p forcedI
                    return c
          loop bs0
      , forceThunk p $ \ p' -> Fix $ Case p' bs0
      ]
    Halt a -> return $ Fix $ Halt a
