module Lang.CPS.Instances.Monads where

import FP
import MAAM
import Lang.CPS.Classes.Delta

----------------------------
-- Flow Sensitivity Monad --
----------------------------

data FSΣ δ μ = FSΣ
  { fsρ :: Env μ
  , fslτ :: LexicalTime μ Ψ
  , fsσ :: Store δ μ
  , fsdτ :: DynamicTime μ Ψ
  }
deriving instance (Eq (Env μ), Eq (LexicalTime μ Ψ), Eq (Store δ μ), Eq (DynamicTime μ Ψ)) => Eq (FSΣ δ μ)
deriving instance (Ord (Env μ), Ord (LexicalTime μ Ψ), Ord (Store δ μ), Ord (DynamicTime μ Ψ)) => Ord (FSΣ δ μ)
instance (AAM μ) => HasBot (FSΣ δ μ) where
  bot = FSΣ
    { fsρ = bot
    , fslτ = LexicalTime $ tzero (P :: P (LexicalTemporal μ))
    , fsσ = bot
    , fsdτ = DynamicTime $ tzero (P :: P (DynamicTemporal μ))
    }
fsρL :: Lens (FSΣ δ μ) (Env μ)
fsρL = lens fsρ $ \ ss ρ -> ss { fsρ = ρ }
fslτL :: Lens (FSΣ δ μ) (LexicalTime μ Ψ)
fslτL = lens fslτ $ \ ss lτ -> ss { fslτ = lτ }
fsσL :: Lens (FSΣ δ μ) (Store δ μ)
fsσL = lens fsσ $ \ ss σ -> ss { fsσ = σ }
fsdτL :: Lens (FSΣ δ μ) (DynamicTime μ Ψ)
fsdτL = lens fsdτ $ \ ss dτ -> ss { fsdτ = dτ }

newtype FlowSensitive δ μ a = FlowSensitive { runFlowSensitive :: StateT (FSΣ δ μ) (ListSetT ID) a }
  deriving 
    ( Unit, Functor, Applicative, Monad
    , MonadZero
    , MonadPlus
    , MonadStateE (FSΣ δ μ)
    )
instance MonadFail (FlowSensitive δ μ) where
  fail = error . fromChars
instance (AAM μ) => MonadStep (FlowSensitive δ μ) where
  type SS (FlowSensitive δ μ) a = SS (StateT (FSΣ δ μ) (ListSetT ID)) a
  type SSC (FlowSensitive δ μ) a = SSC (StateT (FSΣ δ μ) (ListSetT ID)) a
  mstep f = mstep (runFlowSensitive . f)
  munit P = munit (P :: P (StateT (FSΣ δ μ) (ListSetT ID)))
instance MonadStateE (Env μ) (FlowSensitive δ μ) where
  stateE :: StateT (Env μ) (FlowSensitive δ μ) ~> FlowSensitive δ μ
  stateE = (stateE :: StateT (FSΣ δ μ) (FlowSensitive δ μ) ~> FlowSensitive δ μ) . stateLens fsρL
instance MonadStateE (LexicalTime μ Ψ) (FlowSensitive δ μ) where
  stateE :: StateT (LexicalTime μ Ψ) (FlowSensitive δ μ) ~> FlowSensitive δ μ
  stateE = (stateE :: StateT (FSΣ δ μ) (FlowSensitive δ μ) ~> FlowSensitive δ μ) . stateLens fslτL
instance MonadStateE (Store δ μ) (FlowSensitive δ μ) where
  stateE :: StateT (Store δ μ) (FlowSensitive δ μ) ~> FlowSensitive δ μ
  stateE = (stateE :: StateT (FSΣ δ μ) (FlowSensitive δ μ) ~> FlowSensitive δ μ) . stateLens fsσL
instance MonadStateE (DynamicTime μ Ψ) (FlowSensitive δ μ) where
  stateE :: StateT (DynamicTime μ Ψ) (FlowSensitive δ μ) ~> FlowSensitive δ μ
  stateE = (stateE :: StateT (FSΣ δ μ) (FlowSensitive δ μ) ~> FlowSensitive δ μ) . stateLens fsdτL
fsm :: P FlowSensitive
fsm = P

------------------------------
-- Flow Insensitivity Monad --
------------------------------

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

newtype FlowInsensitive δ μ a = FlowInsensitive { runFlowInsensitive :: StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)) a }

deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Unit (FlowInsensitive δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Functor (FlowInsensitive δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Applicative (FlowInsensitive δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => Monad (FlowInsensitive δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadZero (FlowInsensitive δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadPlus (FlowInsensitive δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (FIΣ μ) (FlowInsensitive δ μ)
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadFail (FlowInsensitive δ μ) where
  fail = error . fromChars
instance (AAM μ, Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStep (FlowInsensitive δ μ) where
  type SS (FlowInsensitive δ μ) a = SS (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID))) a
  type SSC (FlowInsensitive δ μ) a = SSC (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID))) a
  mstep f = mstep (runFlowInsensitive . f)
  munit P = munit (P :: P (StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID))))
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (Env μ) (FlowInsensitive δ μ) where
  stateE :: StateT (Env μ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ) . stateLens fiρL
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (LexicalTime μ Ψ) (FlowInsensitive δ μ) where
  stateE :: StateT (LexicalTime μ Ψ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ) . stateLens filτL
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (Store δ μ) (FlowInsensitive δ μ) where
  stateE :: StateT (Store δ μ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ
  stateE = FlowInsensitive . mtMap stateE . stateCommute . mtMap runFlowInsensitive
instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => MonadStateE (DynamicTime μ Ψ) (FlowInsensitive δ μ) where
  stateE :: StateT (DynamicTime μ Ψ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ
  stateE = (stateE :: StateT (FIΣ μ) (FlowInsensitive δ μ) ~> FlowInsensitive δ μ) . stateLens fidτL
fim :: P FlowInsensitive
fim = P
