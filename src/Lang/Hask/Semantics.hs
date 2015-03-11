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
type Store αν lτ dτ = Map (Addr lτ dτ) (αν lτ dτ)

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

data KonMemoClo lτ dτ αν = KonMemoClo
  { konMemoCloLoc :: Addr lτ dτ
  , konMemoCloVal :: αν lτ dτ
  , konMemoCloArg :: Name
  , konMemoCloBody :: Call
  , konMemoCloEnv :: Env lτ dτ
  } deriving (Eq, Ord)

class Val lτ dτ γν αν | αν -> γν where
  botI :: αν lτ dτ
  neg :: αν lτ dτ -> αν lτ dτ
  litI :: Literal -> αν lτ dτ
  litTestE :: Literal -> αν lτ dτ -> γν Bool
  dataI :: Data lτ dτ -> αν lτ dτ
  dataAnyI :: DataCon -> αν lτ dτ
  dataE :: αν lτ dτ -> γν (Data lτ dτ)
  funCloI :: FunClo lτ dτ -> αν lτ dτ
  funCloE :: αν lτ dτ -> γν (FunClo lτ dτ)
  thunkCloI :: ThunkClo lτ dτ -> αν lτ dτ
  thunkCloE :: αν lτ dτ -> γν (ThunkClo lτ dτ)
  forcedI :: αν lτ dτ -> αν lτ dτ
  forcedE :: αν lτ dτ -> γν (αν lτ dτ)
  refI :: Ref lτ dτ -> αν lτ dτ
  refAnyI :: αν lτ dτ
  refE :: αν lτ dτ -> γν (Ref lτ dτ)
  konCloI :: KonClo lτ dτ -> αν lτ dτ
  konCloE :: αν lτ dτ -> γν (KonClo lτ dτ)
  konMemoCloI :: KonMemoClo lτ dτ αν -> αν lτ dτ
  konMemoCloE :: αν lτ dτ -> γν (KonMemoClo lτ dτ αν)

-- State Space

data 𝒮 αν lτ dτ = 𝒮
  { 𝓈Env :: Env lτ dτ
  , 𝓈Store :: Store αν lτ dτ
  , 𝓈Time :: Time lτ dτ
  }
makeLenses ''𝒮

-- Analysis effects and constraints

class
  ( Monad m
  , MonadStateE (𝒮 αν lτ dτ) m
  , MonadZero m
  , MonadPlus m
  , Val lτ dτ Set αν
  , Ord (Addr lτ dτ)
  , JoinLattice (αν lτ dτ)
  , MeetLattice (αν lτ dτ)
  , Temporal lτ
  , Temporal dτ
  ) => Analysis αν lτ dτ m | m -> αν , m -> lτ , m -> dτ where

-- Finite observations on values in the abstract domain

refinePico :: (Analysis αν lτ dτ m) => Pico -> αν lτ dτ -> m ()
refinePico (Var x) v = do
  𝓁 <- alloc x
  modifyL 𝓈StoreL $ mapInsertWith (/\) 𝓁 v
refinePico (Lit _) _ = return ()

extract :: (Analysis αν lτ dτ m) => (a -> αν lτ dτ) -> (αν lτ dτ -> Set a) -> Pico -> αν lτ dτ -> m a
extract intro elim p v = do
  a <- mset $ elim v
  refinePico p $ intro a
  return a

extractIsLit :: (Analysis αν lτ dτ m) => Literal -> Pico -> αν lτ dτ -> m ()
extractIsLit l p v = do
  b <- mset $ litTestE l v
  guard b
  refinePico p $ litI l

-- Time management

tickLex :: (Analysis αν lτ dτ m) => Call -> m ()
tickLex = modifyL (timeLexL <.> 𝓈TimeL) . tick

tickDyn :: (Analysis αν lτ dτ m) => Call -> m ()
tickDyn = modifyL (timeDynL <.> 𝓈TimeL) . tick

alloc :: (Analysis αν lτ dτ m) => Name -> m (Addr lτ dτ)
alloc x = do
  τ <- getL 𝓈TimeL
  return $ Addr x τ

-- Updating values in the store

bindJoin :: (Analysis αν lτ dτ m) => Name -> αν lτ dτ -> m ()
bindJoin x v = do
  𝓁 <- alloc x
  modifyL 𝓈EnvL $ mapInsert x 𝓁
  modifyL 𝓈StoreL $ mapInsertWith (\/) 𝓁 v

updateRef :: (Analysis αν lτ dτ m) => Addr lτ dτ -> αν lτ dτ -> αν lτ dτ -> m ()
updateRef 𝓁 vOld vNew = modifyL 𝓈StoreL $ \ σ -> 
  mapModify (\ v -> v /\ neg vOld) 𝓁 σ \/ mapSingleton 𝓁 vNew

-- Denotations

addr :: (Analysis αν lτ dτ m) => Addr lτ dτ -> m (αν lτ dτ)
addr 𝓁 = do
  σ <- getL 𝓈StoreL
  liftMaybeZero $ σ # 𝓁

var :: (Analysis αν lτ dτ m) => Name -> m (αν lτ dτ)
var x = do
  ρ <- getL 𝓈EnvL
  addr *$ liftMaybeZero $ ρ # x

pico :: (Analysis αν lτ dτ m) => Pico -> m (αν lτ dτ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

atom :: (Analysis αν lτ dτ m) => Atom -> m (αν lτ dτ)
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

forceThunk :: (Analysis αν lτ dτ m) => Pico -> αν lτ dτ -> (Pico -> Call) -> m Call
forceThunk p v mk = do
  Ref x 𝓁 <- extract refI refE p v
  delayv <- addr 𝓁
  msum
    [ do
        v' <- extract forcedI forcedE p delayv
        bindJoin x v'
        return $ mk $ Var x
    , do
        ThunkClo k p₁' p₂' ρ' lτ' <- extract thunkCloI thunkCloE p delayv
        ρ <- getL 𝓈EnvL
        let kv = konMemoCloI $ KonMemoClo 𝓁 delayv x (mk $ Var x) ρ
        putL 𝓈EnvL ρ'
        putL (timeLexL <.> 𝓈TimeL) lτ'
        bindJoin k kv
        return $ Fix $ AppF p₁' p₂' $ Var k
    ]

call :: (Analysis αν lτ dτ m) => Call -> m Call
call c = do
  tickDyn c
  case unFix c of
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
            updateRef 𝓁 v $ forcedI v₂
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
