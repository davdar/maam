module Lang.Lam.CPS.Instances.Monads where

import FP
import MAAM
import Lang.Lam.CPS.Classes.Val

-----------------------------------------
-- Flow Sensitive Path Sensitive Monad --
-----------------------------------------

data FSPSΣ val lτ dτ = FSPSΣ
  { fspsρ :: Env lτ dτ
  , fspslτ :: lτ
  , fspsσ :: Store val lτ dτ
  , fspsdτ :: dτ
  } deriving (Eq, Ord)

fspsρL :: Lens (FSPSΣ val lτ dτ) (Env μ)
fspsρL = lens fspsρ $ \ ss ρ -> ss { fspsρ = ρ }
fspslτL :: Lens (FSPSΣ val lτ dτ) lτ
fspslτL = lens fspslτ $ \ ss lτ -> ss { fspslτ = lτ }
fspsσL :: Lens (FSPSΣ val lτ dτ) (Store δ μ)
fspsσL = lens fspsσ $ \ ss σ -> ss { fspsσ = σ }
fspsdτL :: Lens (FSPSΣ val lτ dτ) dτ
fspsdτL = lens fspsdτ $ \ ss dτ -> ss { fspsdτ = dτ }

newtype FSPS val lτ dτ a = FSPS { runFSPS :: StateT (FSPSΣ val lτ dτ) (SetT ID) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero
    , MonadPlus
    , MonadStateE (FSPSΣ δ μ)
    , MonadStep (SetT :.: ((,) (FSPSΣ val lτ dτ)) :.: ID)
    )
instance MonadStateE (Env μ) (FSPS val lτ dτ) where
  stateE :: StateT (Env μ) (FSPS val lτ dτ) ~> FSPS val lτ dτ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS val lτ dτ) ~> FSPS val lτ dτ) . stateLens fspsρL
instance MonadStateE lτ (FSPS val lτ dτ) where
  stateE :: StateT lτ (FSPS val lτ dτ) ~> FSPS val lτ dτ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS val lτ dτ) ~> FSPS val lτ dτ) . stateLens fspslτL
instance MonadStateE (Store δ μ) (FSPS val lτ dτ) where
  stateE :: StateT (Store δ μ) (FSPS val lτ dτ) ~> FSPS val lτ dτ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS val lτ dτ) ~> FSPS val lτ dτ) . stateLens fspsσL
instance MonadStateE dτ (FSPS val lτ dτ) where
  stateE :: StateT dτ (FSPS val lτ dτ) ~> FSPS val lτ dτ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS val lτ dτ) ~> FSPS val lτ dτ) . stateLens fspsdτL

fspsm :: P FSPS
fspsm = P

runFSPS_SS :: (Ord val, Ord lτ, Ord dτ, Ord a) => (SetT :.: ((,) (FSPSΣ val lτ dτ)) :.: ID) a -> Set (a, FSPSΣ δ μ)
runFSPS_SS = setMap swap . runSetT . runSetT . runCompose . runCompose

-----------------------------------------
-- Flow Sensitive Path Insensitive Monad --
-----------------------------------------

data FSPIΣ lτ dτ = FSPIΣ
  { fspiρ :: Env lτ dτ
  , fspilτ :: lτ
  , fspidτ :: dτ
  } deriving (Eq, Ord)

fspiρL :: Lens (FSPIΣ lτ dτ) (Env μ)
fspiρL = lens fspiρ $ \ ss ρ -> ss { fspiρ = ρ }
fspilτL :: Lens (FSPIΣ lτ dτ) lτ
fspilτL = lens fspilτ $ \ ss lτ -> ss { fspilτ = lτ }
fspidτL :: Lens (FSPIΣ lτ dτ) dτ
fspidτL = lens fspidτ $ \ ss dτ -> ss { fspidτ = dτ }

newtype FSPI val lτ dτ a = FSPI { runFSPI :: AddStateT (FSPIΣ lτ dτ) (SetT (StateT (Store val lτ dτ) ID)) a }
  deriving 
    ( Unit
    , Functor
    , Product
    , Bind
    , Applicative
    , Monad
    , MonadZero
    , MonadPlus
    , MonadStep ()
    , MonadStateE (FSPIΣ lτ dτ, Store val lτ dτ)
    , MonadStateI (FSPIΣ lτ dτ, Store val lτ dτ)
    , MonadState (FSPIΣ lτ dτ, Store val lτ dτ)
    )

fspim :: P FSPI
fspim = P

runFSPI_SS :: (Ord lτ, Ord dτ, Ord (Val δ μ), Ord a) => SS (FSPI δ μ) a -> Set ((a, FSPIΣ lτ dτ), Store δ μ)
runFSPI_SS = cmap (mapFst runPairWith . runPairWith . runID . runCompose) . runCompose . runCompose

----------------------------
-- Flow Insensitive Monad --
----------------------------

data FIΣ lτ dτ = FIΣ
  { fiρ :: Env lτ dτ
  , filτ :: lτ
  , fidτ :: dτ
  } deriving (Eq, Ord)

fiρL :: Lens (FIΣ μ) (Env μ)
fiρL = lens fiρ $ \ ss ρ -> ss { fiρ = ρ }
filτL :: Lens (FIΣ μ) lτ
filτL = lens filτ $ \ ss lτ -> ss { filτ = lτ }
fidτL :: Lens (FIΣ μ) dτ
fidτL = lens fidτ $ \ ss dτ -> ss { fidτ = dτ }

newtype FI val lτ dτ a = FI { runFlowInsensitive :: StateT (FIΣ μ) (ListSetT (StateT (Store val lτ dτ) ID)) a }
  deriving (Unit, Functor, Applicative, Product, Bind, Monad, MonadPlus, MonadZero, MonadPlus, MonadStateE (FIΣ lτ dτ))
instance (AAM μ, Ord lτ, Ord dτ, JoinLattice (Val δ μ)) => MonadStep (FI δ μ) where
  type SS (FI δ μ) = SS (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)))
  type SSC (FI δ μ) = SSC (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)))
  mstep f = mstep (runFlowInsensitive . f)
  munit P = munit (P :: P (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID))))
instance (Ord lτ, Ord dτ, JoinLattice (Val δ μ)) => MonadStateE (Env μ) (FI δ μ) where
  stateE :: StateT (Env μ) (FI δ μ) ~> FI δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FI δ μ) ~> FI δ μ) . stateLens fiρL
instance (Ord lτ, Ord dτ, JoinLattice (Val δ μ)) => MonadStateE lτ (FI δ μ) where
  stateE :: StateT lτ (FI δ μ) ~> FI δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FI δ μ) ~> FI δ μ) . stateLens filτL
instance (Ord lτ, Ord dτ, JoinLattice (Val δ μ)) => MonadStateE (Store δ μ) (FI δ μ) where
  stateE :: StateT (Store δ μ) (FI δ μ) ~> FI δ μ
  stateE = FI . mtMap stateE . stateCommute . mtMap runFlowInsensitive
instance (Ord lτ, Ord dτ, JoinLattice (Val δ μ)) => MonadStateE dτ (FI δ μ) where
  stateE :: StateT dτ (FI δ μ) ~> FI δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FI δ μ) ~> FI δ μ) . stateLens fidτL
fim :: P FI
fim = P

runFI_SS :: (Ord lτ, Ord dτ, Ord a) => SS (FI δ μ) a -> (Set (a, FIΣ μ), Store δ μ)
runFI_SS = mapFst (cmap runPairWith) . runPairWith . runID . runCompose . runCompose . runCompose
