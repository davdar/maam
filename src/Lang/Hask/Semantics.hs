module Lang.Hask.Semantics where

import FP

import Lang.Hask.CPS hiding (atom)
import Name
import Literal
import DataCon
import CoreSyn (AltCon(..))

-- Values

class Temporal τ where
  tzero :: τ
  tick :: Call -> τ -> τ

data Time lτ dτ = Time
  { timeLex :: lτ
  , timeDyn :: dτ
  } deriving (Eq, Ord)
makeLenses ''Time

type Env lτ dτ = Map Name (Addr lτ dτ)
type Store ν lτ dτ = Map (Addr lτ dτ) (ν lτ dτ)

data Addr lτ dτ = Addr
  { addrName :: Name
  , addrTime :: Time lτ dτ
  } deriving (Eq, Ord)

data Data lτ dτ = Data
  { dataCon :: DataCon
  , dataArgs :: [Addr lτ dτ]
  } deriving (Eq, Ord)

data FunClo lτ dτ = FunClo
  { funCloLamArg :: Name
  , funCloKonArg :: Name
  , funCloBody :: Call
  , funCloEnv :: Env lτ dτ
  , funCloTime :: lτ
  } deriving (Eq, Ord)

data ThunkClo lτ dτ = ThunkClo
  { thunkCloKonArg :: Name
  , thunkCloFun :: Pico
  , thunkCloArg :: Pico
  , thunkCloEnv :: Env lτ dτ
  , thunkCloTime :: lτ
  } deriving (Eq, Ord)

data Ref lτ dτ = Ref
  { refName :: Name
  , refAddr :: Addr lτ dτ
  } deriving (Eq, Ord)

data KonClo lτ dτ = KonClo
  { konCloArg :: Name
  , konCloBody :: Call
  , konCloEnv :: Env lτ dτ
  } deriving (Eq, Ord)

data KonMemoClo lτ dτ ν = KonMemoClo
  { konMemoCloLoc :: Addr lτ dτ
  , konMemoCloVal :: ν lτ dτ
  , konMemoCloArg :: Name
  , konMemoCloBody :: Call
  , konMemoCloEnv :: Env lτ dτ
  } deriving (Eq, Ord)

class Val ν lτ dτ where
  botI :: ν lτ dτ
  neg :: ν lτ dτ -> ν lτ dτ
  litI :: Literal -> ν lτ dτ
  litTestE :: Literal -> ν lτ dτ -> Set Bool
  dataI :: Data lτ dτ -> ν lτ dτ
  dataAnyI :: DataCon -> ν lτ dτ
  dataE :: ν lτ dτ -> Maybe (Set (Data lτ dτ))
  funCloI :: FunClo lτ dτ -> ν lτ dτ
  funCloE :: ν lτ dτ -> Maybe (Set (FunClo lτ dτ))
  thunkCloI :: ThunkClo lτ dτ -> ν lτ dτ
  thunkCloE :: ν lτ dτ -> Maybe (Set (ThunkClo lτ dτ))
  forcedI :: ν lτ dτ -> ν lτ dτ
  forcedE :: ν lτ dτ -> Maybe (Set (ν lτ dτ))
  refI :: Ref lτ dτ -> ν lτ dτ
  refAnyI :: ν lτ dτ
  refE :: ν lτ dτ -> Maybe (Set (Ref lτ dτ))
  konCloI :: KonClo lτ dτ -> ν lτ dτ
  konCloE :: ν lτ dτ -> Maybe (Set (KonClo lτ dτ))
  konMemoCloI :: KonMemoClo lτ dτ ν -> ν lτ dτ
  konMemoCloE :: ν lτ dτ -> Maybe (Set (KonMemoClo lτ dτ ν))

-- State Space

data 𝒮 ν lτ dτ = 𝒮
  { 𝓈Env :: Env lτ dτ
  , 𝓈Store :: Store ν lτ dτ
  , 𝓈Time :: Time lτ dτ
  }
makeLenses ''𝒮

-- Analysis effects and constraints

class
  ( Monad m
  , MonadStateE (𝒮 ν lτ dτ) m
  , MonadZero m
  , MonadTop m
  , MonadPlus m
  , Val ν lτ dτ
  , Ord (Addr lτ dτ)
  , JoinLattice (ν lτ dτ)
  , MeetLattice (ν lτ dτ)
  , Temporal lτ
  , Temporal dτ
  ) => Analysis ν lτ dτ m | m -> ν , m -> lτ , m -> dτ where

-- Finite observations on values in the abstract domain

refinePico :: (Analysis ν lτ dτ m) => Pico -> ν lτ dτ -> m ()
refinePico (Var x) v = do
  𝓁 <- alloc x
  modifyL 𝓈StoreL $ mapInsertWith (/\) 𝓁 v
refinePico (Lit _) _ = return ()

extract :: (Analysis ν lτ dτ m) => (a -> ν lτ dτ) -> (ν lτ dτ -> Maybe (Set a)) -> Pico -> ν lτ dτ -> m a
extract intro elim p v = do
  a <- elimMaybe mtop mset $ elim v
  refinePico p $ intro a
  return a

extractIsLit :: (Analysis ν lτ dτ m) => Literal -> Pico -> ν lτ dτ -> m ()
extractIsLit l p v = do
  b <- mset $ litTestE l v
  guard b
  refinePico p $ litI l

-- Time management

tickLex :: (Analysis ν lτ dτ m) => Call -> m ()
tickLex = modifyL (timeLexL <.> 𝓈TimeL) . tick

tickDyn :: (Analysis ν lτ dτ m) => Call -> m ()
tickDyn = modifyL (timeDynL <.> 𝓈TimeL) . tick

alloc :: (Analysis ν lτ dτ m) => Name -> m (Addr lτ dτ)
alloc x = do
  τ <- getL 𝓈TimeL
  return $ Addr x τ

-- Updating values in the store

bindJoin :: (Analysis ν lτ dτ m) => Name -> ν lτ dτ -> m ()
bindJoin x v = do
  𝓁 <- alloc x
  modifyL 𝓈EnvL $ mapInsert x 𝓁
  modifyL 𝓈StoreL $ mapInsertWith (\/) 𝓁 v

updateRef :: (Analysis ν lτ dτ m) => Addr lτ dτ -> ν lτ dτ -> ν lτ dτ -> m ()
updateRef 𝓁 vOld vNew = modifyL 𝓈StoreL $ \ σ -> 
  mapModify (\ v -> v /\ neg vOld) 𝓁 σ \/ mapSingleton 𝓁 vNew

-- Denotations

addr :: (Analysis ν lτ dτ m) => Addr lτ dτ -> m (ν lτ dτ)
addr 𝓁 = do
  σ <- getL 𝓈StoreL
  liftMaybeZero $ σ # 𝓁

var :: (Analysis ν lτ dτ m) => Name -> m (ν lτ dτ)
var x = do
  ρ <- getL 𝓈EnvL
  addr *$ liftMaybeZero $ ρ # x

pico :: (Analysis ν lτ dτ m) => Pico -> m (ν lτ dτ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

atom :: (Analysis ν lτ dτ m) => Atom -> m (ν lτ dτ)
atom = \ case
  Pico p -> pico p
  LamF x k c -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL $ timeLexL <.> 𝓈TimeL
    return $ funCloI $ FunClo x k c ρ lτ
  LamK x c -> do
    ρ <- getL 𝓈EnvL
    return $ konCloI $ KonClo x c ρ
  Thunk r xr k p₁ p₂ -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL $ timeLexL <.> 𝓈TimeL
    𝓁 <- alloc r
    updateRef 𝓁 botI $ thunkCloI $ ThunkClo k p₁ p₂ ρ lτ
    return $ refI $ Ref xr 𝓁

forceThunk :: (Analysis ν lτ dτ m) => Pico -> ν lτ dτ -> (Pico -> Call) -> m Call
forceThunk p v mk = do
  Ref x 𝓁 <- extract refI refE p v
  delayv <- addr 𝓁
  msum
    [ do
        v' <- extract forcedI forcedE p delayv
        bindJoin x v'
        return $ mk $ Var x
    , do
        ThunkClo k p₁' p₂' ρ lτ <- extract thunkCloI thunkCloE p delayv
        putL 𝓈EnvL ρ
        putL (timeLexL <.> 𝓈TimeL) lτ
        kv <- atom $ LamK x $ mk $ Var x
        bindJoin k kv
        return $ Fix $ AppF p₁' p₂' $ Var k
    ]

call :: (Analysis ν lτ dτ m) => Call -> m Call
call c = do
  tickDyn c
  case runFix c of
    Let x a c' -> do
      v <- atom a  
      bindJoin x v
      return c'
    Rec rxrxs c' -> do
      traverseOn rxrxs $ \ (r,xr,x) -> do
        𝓁 <- alloc r
        bindJoin x $ refI $ Ref xr 𝓁
      return c'
    Letrec xas c' -> do
      traverseOn xas $ \ (x, a) -> do
        Ref _xr 𝓁 <- extract refI refE (Var x) *$ pico $ Var x
        updateRef 𝓁 botI *$ atom a
      return c'
    AppK p₁ p₂ -> do
      v₁ <- pico p₁
      v₂ <- pico p₂
      msum
        [ do
            KonClo x c' ρ <- extract konCloI konCloE p₁ v₁
            putL 𝓈EnvL ρ
            bindJoin x v₂
            return c'
        , do
            KonMemoClo 𝓁 v x c' ρ <- extract konMemoCloI konMemoCloE p₁ v₁
            updateRef 𝓁 v v₂
            putL 𝓈EnvL ρ
            bindJoin x v₂
            return c'
        ]
    AppF p₁ p₂ p₃ -> do
      v₁ <- pico p₁
      v₂ <- pico p₂
      v₃ <- pico p₃
      msum
        [ do
            FunClo x k c' ρ lτ <- extract funCloI funCloE p₁ v₁
            putL 𝓈EnvL ρ
            putL (timeLexL <.> 𝓈TimeL) lτ
            bindJoin x v₂
            bindJoin k v₃
            return c'
        , forceThunk p₁ v₁ $ \ p -> Fix $ AppF p p₂ p₃
        ]
    Case p bs0 -> do
      v <- pico p
      msum
        [ do
            -- loop through the alternatives
            let loop bs = do
                  (CaseBranch acon xs c', bs') <- liftMaybeZero $ coerce consL bs
                  case acon of
                    DataAlt con -> msum
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
                          refinePico p $ neg $ dataAnyI con
                          loop bs'
                      ]
                    LitAlt l -> msum
                      -- The alt is a Lit and the value is the same lit; jump to
                      -- the alt body.
                      [ do
                          extractIsLit l p v
                          return c'
                      -- The alt is a Lit and and the value is not the same lit;
                      -- try the next branch.
                      , do
                          refinePico p $ neg $ litI l
                          loop bs'
                      ]
                    -- The alt is the default branch; jump to the body _only if
                    -- the value is not a ref_.
                    DEFAULT -> do
                      refinePico p $ neg $ refAnyI
                      return c
            loop bs0
        , forceThunk p v $ \ p' -> Fix $ Case p' bs0
        ]
    Halt a -> return $ Fix $ Halt a
