module Lang.CPS.Instances.Monads where

import FP
import MAAM
import Lang.CPS.Classes.Delta

-----------------------------------------
-- Flow Sensitive Path Sensitive Monad --
-----------------------------------------

data FSPSΣ δ μ = FSPSΣ
  { fspsρ :: Env μ
  , fspslτ :: LexicalTime μ Ψ
  , fspsσ :: Store δ μ
  , fspsdτ :: DynamicTime μ Ψ
  }
deriving instance (Eq (Env μ), Eq (LexicalTime μ Ψ), Eq (Val δ μ), Eq (DynamicTime μ Ψ)) => Eq (FSPSΣ δ μ)
deriving instance (Ord (Env μ), Ord (LexicalTime μ Ψ), Ord (Val δ μ), Ord (DynamicTime μ Ψ)) => Ord (FSPSΣ δ μ)
instance (AAM μ) => HasBot (FSPSΣ δ μ) where
  bot = FSPSΣ
    { fspsρ = bot
    , fspslτ = LexicalTime $ tzero (P :: P (LexicalTemporal μ))
    , fspsσ = bot
    , fspsdτ = DynamicTime $ tzero (P :: P (DynamicTemporal μ))
    }
fspsρL :: Lens (FSPSΣ δ μ) (Env μ)
fspsρL = lens fspsρ $ \ ss ρ -> ss { fspsρ = ρ }
fspslτL :: Lens (FSPSΣ δ μ) (LexicalTime μ Ψ)
fspslτL = lens fspslτ $ \ ss lτ -> ss { fspslτ = lτ }
fspsσL :: Lens (FSPSΣ δ μ) (Store δ μ)
fspsσL = lens fspsσ $ \ ss σ -> ss { fspsσ = σ }
fspsdτL :: Lens (FSPSΣ δ μ) (DynamicTime μ Ψ)
fspsdτL = lens fspsdτ $ \ ss dτ -> ss { fspsdτ = dτ }

newtype FSPS δ μ a = FSPS { runFSPS :: StateT (FSPSΣ δ μ) (ListSetT ID) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero
    , MonadPlus
    , MonadStateE (FSPSΣ δ μ)
    )
instance MonadFail (FSPS δ μ) where
  fail = error . fromChars
instance (AAM μ) => MonadStep (FSPS δ μ) where
  type SS (FSPS δ μ) = SS (StateT (FSPSΣ δ μ) (ListSetT ID))
  type SSC (FSPS δ μ) = SSC (StateT (FSPSΣ δ μ) (ListSetT ID))
  mstep f = mstep (runFSPS . f)
  munit P = munit (P :: P (StateT (FSPSΣ δ μ) (ListSetT ID)))
instance MonadStateE (Env μ) (FSPS δ μ) where
  stateE :: StateT (Env μ) (FSPS δ μ) ~> FSPS δ μ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS δ μ) ~> FSPS δ μ) . stateLens fspsρL
instance MonadStateE (LexicalTime μ Ψ) (FSPS δ μ) where
  stateE :: StateT (LexicalTime μ Ψ) (FSPS δ μ) ~> FSPS δ μ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS δ μ) ~> FSPS δ μ) . stateLens fspslτL
instance MonadStateE (Store δ μ) (FSPS δ μ) where
  stateE :: StateT (Store δ μ) (FSPS δ μ) ~> FSPS δ μ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS δ μ) ~> FSPS δ μ) . stateLens fspsσL
instance MonadStateE (DynamicTime μ Ψ) (FSPS δ μ) where
  stateE :: StateT (DynamicTime μ Ψ) (FSPS δ μ) ~> FSPS δ μ
  stateE = (stateE :: StateT (FSPSΣ δ μ) (FSPS δ μ) ~> FSPS δ μ) . stateLens fspsdτL
fspsm :: P FSPS
fspsm = P

runFSPS_SS :: (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), Ord (Val δ μ), Ord a) => SS (FSPS δ μ) a -> Set (a, FSPSΣ δ μ)
runFSPS_SS = cmap runPairWith . runID . runCompose . runCompose

-----------------------------------------
-- Flow Sensitive Path Insensitive Monad --
-----------------------------------------

data FSPIΣ μ = FSPIΣ
  { fspiρ :: Env μ
  , fspilτ :: LexicalTime μ Ψ
  , fspidτ :: DynamicTime μ Ψ
  }
deriving instance (Eq (Env μ), Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (FSPIΣ μ)
deriving instance (Ord (Env μ), Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (FSPIΣ μ)
instance (AAM μ) => HasBot (FSPIΣ μ) where
  bot = FSPIΣ
    { fspiρ = bot
    , fspilτ = LexicalTime $ tzero (P :: P (LexicalTemporal μ))
    , fspidτ = DynamicTime $ tzero (P :: P (DynamicTemporal μ))
    }
fspiρL :: Lens (FSPIΣ μ) (Env μ)
fspiρL = lens fspiρ $ \ ss ρ -> ss { fspiρ = ρ }
fspilτL :: Lens (FSPIΣ μ) (LexicalTime μ Ψ)
fspilτL = lens fspilτ $ \ ss lτ -> ss { fspilτ = lτ }
fspidτL :: Lens (FSPIΣ μ) (DynamicTime μ Ψ)
fspidτL = lens fspidτ $ \ ss dτ -> ss { fspidτ = dτ }

newtype FSPI δ μ a = FSPI { runFSPI :: StateT (FSPIΣ μ) (ForkLT (StateT (Store δ μ) ID)) a }
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Unit (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Functor (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Product (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Bind (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Applicative (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Monad (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadZero (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadPlus (FSPI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (FSPIΣ μ) (FSPI δ μ)
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadFail (FSPI δ μ) where
  fail = error . fromChars
instance (AAM μ, Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStep (FSPI δ μ) where
  type SS (FSPI δ μ) = SS (StateT (FSPIΣ μ) (ForkLT (StateT (Store δ μ) ID)))
  type SSC (FSPI δ μ) = SSC (StateT (FSPIΣ μ) (ForkLT (StateT (Store δ μ) ID)))
  mstep f = mstep (runFSPI . f)
  munit P = munit (P :: P (StateT (FSPIΣ μ) (ForkLT (StateT (Store δ μ) ID))))
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (Env μ) (FSPI δ μ) where
  stateE :: StateT (Env μ) (FSPI δ μ) ~> FSPI δ μ
  stateE = (stateE :: StateT (FSPIΣ μ) (FSPI δ μ) ~> FSPI δ μ) . stateLens fspiρL
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (LexicalTime μ Ψ) (FSPI δ μ) where
  stateE :: StateT (LexicalTime μ Ψ) (FSPI δ μ) ~> FSPI δ μ
  stateE = (stateE :: StateT (FSPIΣ μ) (FSPI δ μ) ~> FSPI δ μ) . stateLens fspilτL
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (Store δ μ) (FSPI δ μ) where
  stateE :: StateT (Store δ μ) (FSPI δ μ) ~> FSPI δ μ
  stateE = FSPI . mtMap stateE . stateCommute . mtMap runFSPI
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (DynamicTime μ Ψ) (FSPI δ μ) where
  stateE :: StateT (DynamicTime μ Ψ) (FSPI δ μ) ~> FSPI δ μ
  stateE = (stateE :: StateT (FSPIΣ μ) (FSPI δ μ) ~> FSPI δ μ) . stateLens fspidτL
fspim :: P FSPI
fspim = P

runFSPI_SS :: (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), Ord (Val δ μ), Ord a) => SS (FSPI δ μ) a -> Set ((a, FSPIΣ μ), Store δ μ)
runFSPI_SS = cmap (mapFst runPairWith . runPairWith . runID . runCompose) . runCompose . runCompose

----------------------------
-- Flow Insensitive Monad --
----------------------------

data FIΣ μ = FIΣ
  { fiρ :: Env μ
  , filτ :: LexicalTime μ Ψ
  , fidτ :: DynamicTime μ Ψ
  }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (FIΣ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (FIΣ μ)
instance (AAM μ) => HasBot (FIΣ μ) where
  bot = FIΣ
    { fiρ = bot
    , filτ = LexicalTime $ tzero (P :: P (LexicalTemporal μ))
    , fidτ = DynamicTime $ tzero (P :: P (DynamicTemporal μ))
    }
fiρL :: Lens (FIΣ μ) (Env μ)
fiρL = lens fiρ $ \ ss ρ -> ss { fiρ = ρ }
filτL :: Lens (FIΣ μ) (LexicalTime μ Ψ)
filτL = lens filτ $ \ ss lτ -> ss { filτ = lτ }
fidτL :: Lens (FIΣ μ) (DynamicTime μ Ψ)
fidτL = lens fidτ $ \ ss dτ -> ss { fidτ = dτ }

newtype FI δ μ a = FI { runFlowInsensitive :: StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)) a }
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Unit (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Functor (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Applicative (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Product (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Bind (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Monad (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadZero (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadPlus (FI δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (FIΣ μ) (FI δ μ)
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadFail (FI δ μ) where
  fail = error . fromChars
instance (AAM μ, Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStep (FI δ μ) where
  type SS (FI δ μ) = SS (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)))
  type SSC (FI δ μ) = SSC (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)))
  mstep f = mstep (runFlowInsensitive . f)
  munit P = munit (P :: P (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID))))
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (Env μ) (FI δ μ) where
  stateE :: StateT (Env μ) (FI δ μ) ~> FI δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FI δ μ) ~> FI δ μ) . stateLens fiρL
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (LexicalTime μ Ψ) (FI δ μ) where
  stateE :: StateT (LexicalTime μ Ψ) (FI δ μ) ~> FI δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FI δ μ) ~> FI δ μ) . stateLens filτL
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (Store δ μ) (FI δ μ) where
  stateE :: StateT (Store δ μ) (FI δ μ) ~> FI δ μ
  stateE = FI . mtMap stateE . stateCommute . mtMap runFlowInsensitive
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (DynamicTime μ Ψ) (FI δ μ) where
  stateE :: StateT (DynamicTime μ Ψ) (FI δ μ) ~> FI δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FI δ μ) ~> FI δ μ) . stateLens fidτL
fim :: P FI
fim = P

runFI_SS :: (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), Ord a) => SS (FI δ μ) a -> (Set (a, FIΣ μ), Store δ μ)
runFI_SS = mapFst (cmap runPairWith) . runPairWith . runID . runCompose . runCompose . runCompose
