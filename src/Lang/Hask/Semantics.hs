module Lang.Hask.Semantics where

import FP

import Lang.Hask.CPS hiding (atom)
import Name
import Literal
import DataCon
import CoreSyn (AltCon(..))

class Time ψ τ | τ -> ψ where
  tzero :: τ
  tick :: ψ -> τ -> τ

-- Values

data Moment lτ dτ = Moment
  { timeLex :: lτ
  , timeDyn :: dτ
  } deriving (Eq, Ord)
makeLenses ''Moment
instance (Time ψ lτ, Time ψ dτ) => Bot (Moment lτ dτ) where bot = Moment tzero tzero

data Addr lτ dτ = Addr
  { addrName :: Name
  , addrTime :: Moment lτ dτ
  } deriving (Eq, Ord)

type Env lτ dτ = Map Name (Addr lτ dτ)
type Store ν lτ dτ = Map (Addr lτ dτ) (ν lτ dτ)

data ArgVal lτ dτ =
    AddrVal (Addr lτ dτ)
  | LitVal Literal
  deriving (Eq, Ord)

data Data lτ dτ = Data
  { dataCon :: DataCon
  , dataArgs :: [ArgVal lτ dτ]
  } deriving (Eq, Ord)

data FunClo lτ dτ = FunClo
  { funCloLamArg :: Name
  , funCloKonArg :: Name
  , funCloBody :: Call
  , funCloEnv :: Env lτ dτ
  , funCloTime :: lτ
  } deriving (Eq, Ord)

data Ref lτ dτ = Ref
  { refAddr :: Addr lτ dτ
  } deriving (Eq, Ord)

data KonClo lτ dτ = KonClo
  { konCloArg :: Name
  , konCloBody :: Call
  , konCloEnv :: Env lτ dτ
  } deriving (Eq, Ord)

data KonMemoClo lτ dτ = KonMemoClo
  { konMemoCloLoc :: Addr lτ dτ
  , konMemoCloThunk :: ThunkClo lτ dτ
  , konMemoCloArg :: Name
  , konMemoCloBody :: Call
  , konMemoCloEnv :: Env lτ dτ
  } deriving (Eq, Ord)

data Forced lτ dτ = Forced
  { forcedVal :: ArgVal lτ dτ
  } deriving (Eq, Ord)

data ThunkClo lτ dτ = ThunkClo
  { thunkCloKonXLoc :: Int
  , thunkCloKonXArg :: Name
  , thunkCloKonKArg :: Name
  , thunkCloFun :: Pico
  , thunkCloArg :: Pico
  , thunkCloEnv :: Env lτ dτ
  , thunkCloTime :: lτ
  } deriving (Eq, Ord)

class Val lτ dτ γν αν | αν -> γν where
  botI :: αν lτ dτ
  litI :: Literal -> αν lτ dτ
  litTestE :: Literal -> αν lτ dτ -> γν Bool
  dataI :: Data lτ dτ -> αν lτ dτ
  dataAnyI :: DataCon -> αν lτ dτ
  dataE :: αν lτ dτ -> γν (Data lτ dτ)
  funCloI :: FunClo lτ dτ -> αν lτ dτ
  funCloE :: αν lτ dτ -> γν (FunClo lτ dτ)
  refI :: Ref lτ dτ -> αν lτ dτ
  refAnyI :: αν lτ dτ
  refE :: αν lτ dτ -> γν (Ref lτ dτ)
  konCloI :: KonClo lτ dτ -> αν lτ dτ
  konCloE :: αν lτ dτ -> γν (KonClo lτ dτ)
  konMemoCloI :: KonMemoClo lτ dτ -> αν lτ dτ
  konMemoCloE :: αν lτ dτ -> γν (KonMemoClo lτ dτ)
  thunkCloI :: ThunkClo lτ dτ -> αν lτ dτ
  thunkCloE :: αν lτ dτ -> γν (ThunkClo lτ dτ)
  forcedI :: Forced lτ dτ -> αν lτ dτ
  forcedE :: αν lτ dτ -> γν (Forced lτ dτ)

-- State Space

data 𝒮 ν lτ dτ = 𝒮
  { 𝓈Env :: Env lτ dτ
  , 𝓈Store :: Store ν lτ dτ
  , 𝓈Time :: Moment lτ dτ
  } deriving (Eq, Ord)
instance (Time ψ lτ, Time ψ dτ) => Bot (𝒮 ν lτ dτ) where bot = 𝒮 bot bot bot
makeLenses ''𝒮

-- Analysis effects and constraints

type TimeC lτ dτ = (Ord lτ, Ord dτ, Time Int lτ, Time Int dτ)
type ValC ν lτ dτ = (JoinLattice (ν lτ dτ), Meet (ν lτ dτ), Neg (ν lτ dτ), Val lτ dτ SetWithTop ν)
type MonadC ν lτ dτ m = (Monad m, MonadBot m, MonadTop m, MonadPlus m, MonadState (𝒮 ν lτ dτ) m)

class ( MonadC ν lτ dτ m , ValC ν lτ dτ , TimeC lτ dτ) => Analysis ν lτ dτ m | m -> ν , m -> lτ , m -> dτ

-- Moment management

tickLex :: (Analysis ν lτ dτ m) => Call -> m ()
tickLex = modifyL (timeLexL <.> 𝓈TimeL) . tick . stampedFixID

tickDyn :: (Analysis ν lτ dτ m) => Call -> m ()
tickDyn = modifyL (timeDynL <.> 𝓈TimeL) . tick . stampedFixID

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

-- Refinement and extraction

refine :: (Analysis ν lτ dτ m) => ArgVal lτ dτ -> ν lτ dτ -> m ()
refine (AddrVal 𝓁) v = modifyL 𝓈StoreL $ mapInsertWith (/\) 𝓁 v
refine (LitVal _) _ = return ()

extract :: (Analysis ν lτ dτ m) => (a -> ν lτ dτ) -> (ν lτ dτ -> SetWithTop a) -> ArgVal lτ dτ -> m a
extract intro elim av = do
  v <- argVal av
  a <- setWithTopElim mtop mset $ elim v
  refine av $ intro a
  return a

extractIsLit :: (Analysis ν lτ dτ m) => Literal -> ArgVal lτ dτ -> m ()
extractIsLit l av = do
  v <- argVal av
  b <- setWithTopElim mtop mset $ litTestE l v
  guard b
  refine av $ litI l

-- Denotations

addr :: (Analysis ν lτ dτ m) => Addr lτ dτ -> m (ν lτ dτ)
addr 𝓁 = do
  σ <- getL 𝓈StoreL
  maybeZero $ σ # 𝓁

argVal :: (Analysis ν lτ dτ m) => ArgVal lτ dτ -> m (ν lτ dτ)
argVal (AddrVal 𝓁) = addr 𝓁
argVal (LitVal l) = return $ litI l

varAddr :: (Analysis ν lτ dτ m) => Name -> m (Addr lτ dτ)
varAddr x = do
  ρ <- getL 𝓈EnvL
  maybeZero $ ρ # x

var :: (Analysis ν lτ dτ m) => Name -> m (ν lτ dτ)
var = addr *. varAddr

pico :: (Analysis ν lτ dτ m) => Pico -> m (ν lτ dτ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

picoArg :: (Analysis ν lτ dτ m) => Pico -> m (ArgVal lτ dτ)
picoArg (Var x) = AddrVal ^$ varAddr x
picoArg (Lit l) = return $ LitVal l

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
  Thunk r xi x k p₁ p₂ -> do
    ρ <- getL 𝓈EnvL
    lτ <- getL $ timeLexL <.> 𝓈TimeL
    𝓁 <- alloc r
    updateRef 𝓁 botI $ thunkCloI $ ThunkClo xi x k p₁ p₂ ρ lτ
    return $ refI $ Ref 𝓁

forceThunk :: forall ν lτ dτ m. (Analysis ν lτ dτ m) => Name -> ArgVal lτ dτ -> Call -> m Call
forceThunk x av c = do
  Ref 𝓁 <- extract refI refE av
  msum
    [ do
        Forced av' <- extract forcedI forcedE $ AddrVal 𝓁
        v' <- argVal av'
        bindJoin x v'
        return c
    , do
        t@(ThunkClo xi' x' k p₁' p₂' ρ' lτ') <- extract thunkCloI thunkCloE $ AddrVal 𝓁
        ρ <- getL 𝓈EnvL
        let kv = konMemoCloI $ KonMemoClo 𝓁 t x c ρ
        putL 𝓈EnvL ρ'
        putL (timeLexL <.> 𝓈TimeL) lτ'
        bindJoin k kv
        return $ StampedFix xi' $ AppF xi' x' p₁' p₂' $ Var k
    ]

call :: (Analysis ν lτ dτ m) => Call -> m Call
call c = do
  tickDyn c
  case stampedFix c of
    Let x a c' -> do
      v <- atom a  
      bindJoin x v
      return c'
    Rec rxs c' -> do
      traverseOn rxs $ \ (r,x) -> do
        𝓁 <- alloc r
        bindJoin x $ refI $ Ref 𝓁
      return c'
    Letrec xas c' -> do
      traverseOn xas $ \ (x, a) -> do
        av <- picoArg $ Var x
        Ref 𝓁 <- extract refI refE av
        updateRef 𝓁 botI *$ atom a
      return c'
    AppK p₁ p₂ -> do
      av₁ <- picoArg p₁
      v₂ <- pico p₂
      msum
        [ do
            KonClo x c' ρ <- extract konCloI konCloE av₁
            putL 𝓈EnvL ρ
            bindJoin x v₂
            return c'
        , do
            KonMemoClo 𝓁 th x c' ρ <- extract konMemoCloI konMemoCloE av₁
            updateRef 𝓁 (thunkCloI th) . forcedI . Forced *$ picoArg p₂
            putL 𝓈EnvL ρ
            bindJoin x v₂
            return c'
        ]
    AppF xi' x' p₁ p₂ p₃ -> do
      av₁ <- picoArg p₁
      v₂ <- pico p₂
      v₃ <- pico p₃
      msum
        [ do
            FunClo x k c' ρ lτ <- extract funCloI funCloE av₁
            putL 𝓈EnvL ρ
            putL (timeLexL <.> 𝓈TimeL) lτ
            bindJoin x v₂
            bindJoin k v₃
            return c'
        , forceThunk x' av₁ $ StampedFix xi' $ AppF xi' x' (Var x') p₂ p₃
        ]
    Case xi' x' p bs0 -> do
      av <- picoArg p
      msum
        [ do
            -- loop through the alternatives
            let loop bs = do
                  (CaseBranch acon xs c', bs') <- maybeZero $ view consL bs
                  case acon of
                    DataAlt con -> msum
                      -- The alt is a Data and the value is a Data with the same
                      -- tag; jump to the alt body.
                      [ do
                          Data dcon 𝓁s <- extract dataI dataE av
                          guard $ con == dcon
                          x𝓁s <- maybeZero $ zip xs 𝓁s
                          traverseOn x𝓁s $ \ (x, av') -> do
                            v' <- argVal av'
                            bindJoin x v'
                          return c'
                      -- The alt is a Data and the value is not a Data with the
                      -- same tag; try the next branch.
                      , do
                          refine av $ neg $ dataAnyI con
                          loop bs'
                      ]
                    LitAlt l -> msum
                      -- The alt is a Lit and the value is the same lit; jump to
                      -- the alt body.
                      [ do
                          extractIsLit l av
                          return c'
                      -- The alt is a Lit and and the value is not the same lit;
                      -- try the next branch.
                      , do
                          refine av $ neg $ litI l
                          loop bs'
                      ]
                    -- The alt is the default branch; jump to the body _only if
                    -- the value is not a ref_.
                    DEFAULT -> do
                      refine av $ neg $ refAnyI
                      return c
            loop bs0
        , forceThunk x' av $ StampedFix xi' $ Case xi' x' (Var x') bs0
        ]
    Halt _ -> return c
