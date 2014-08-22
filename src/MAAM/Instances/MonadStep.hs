module MAAM.Instances.MonadStep where

import FP
import MAAM.Classes.MonadStep

instance MonadStep ID where
  type SS ID = ID
  type SSC ID = Universal
  mstep :: (SSC ID a, SSC ID b) => (a -> ID b) -> (SS ID a -> SS ID b)
  mstep f = f . runID
  munit :: (SSC ID a) => P ID -> a -> SS ID a
  munit P = ID

instance (MonadStep m, Functorial JoinLattice m) => MonadStep (ListSetT m) where
  type SS (ListSetT m) = SS m :.: Set
  type SSC (ListSetT m) = Ord ::*:: (SSC m ::.:: Set)
  mstep :: (SSC (ListSetT m) a, SSC (ListSetT m) b) => (a -> ListSetT m b) -> (SS (ListSetT m) a -> SS (ListSetT m) b)
  mstep f = mapCompose $ mstep $ mmap sset . runListSetT . msums . map f . toList
  munit :: (SSC (ListSetT m) a) => P (ListSetT m) -> a -> SS (ListSetT m) a
  munit P = Compose . munit (P :: P m) . ssingleton

newtype ForkT m a = ForkT { runForkT :: ListSetT m a }
  deriving (Unit, Functor)
deriving instance (Monad m, Functorial JoinLattice m) => Applicative (ForkT m)
deriving instance (Monad m, Functorial JoinLattice m) => Monad (ForkT m)
deriving instance (Monad m, Functorial JoinLattice m) => MonadZero (ForkT m)
deriving instance (Monad m, Functorial JoinLattice m) => MonadPlus (ForkT m)
deriving instance (Monad m, Functorial JoinLattice m, MonadStateE s m, JoinLattice s) => MonadStateE s (ForkT m)
deriving instance (Monad m, Functorial JoinLattice m, MonadStateI s m, JoinLattice s) => MonadStateI s (ForkT m)
deriving instance (Monad m, Functorial JoinLattice m, MonadState s m, JoinLattice s) => MonadState s (ForkT m)
instance (MonadStep m, Functorial JoinLattice m, CFunctorM (SSC m) (SS m)) => MonadStep (ForkT m) where
  type SS (ForkT m) = Set :.: SS m
  type SSC (ForkT m) = (Ord ::.:: SS m) ::*:: SSC m ::*:: (SSC m ::.:: ListSet)
  mstep :: (SSC (ForkT m) a, SSC (ForkT m) b) => (a -> ForkT m b) -> (SS (ForkT m) a -> SS (ForkT m) b)
  mstep f = mapCompose $ cextend $ sset . runListSet . csequence . mstep (runListSetT . runForkT . f)
  munit :: (SSC (ForkT m) a) => P (ForkT m) -> a -> SS (ForkT m) a
  munit P = Compose . ssingleton . munit (P :: P m)

newtype PairWith s a = PairWith { runPairWith :: (a, s) }
  deriving (Eq, Ord, PartialOrder, HasBot, JoinLattice)
mapPairWith :: ((a, s) -> (b, s)) -> PairWith s a -> PairWith s b
mapPairWith f = PairWith . f . runPairWith
mapPairWithM :: (Functor m) => ((a, s) -> m (b, s)) -> PairWith s a -> m (PairWith s b)
mapPairWithM f = map PairWith . f . runPairWith
instance Functor (PairWith s) where
  map = mapPairWith . mapFst
instance FunctorM (PairWith s) where
  mapM = mapPairWithM . mapFstM
instance (MonadStep m, HasBot s) => MonadStep (StateT s m) where
  type SS (StateT s m) = SS m :.: PairWith s
  type SSC (StateT s m) = SSC m ::.:: PairWith s
  mstep :: forall a b. (SSC (StateT s m) a, SSC (StateT s m) b) => (a -> StateT s m b) -> (SS (StateT s m) a -> SS (StateT s m) b)
  mstep f = mapCompose $
     mstep $ \ (runPairWith -> (a, s)) -> map PairWith $ unStateT (f a) s
  munit :: forall a. (SSC (StateT s m) a) => P (StateT s m) -> a -> SS (StateT s m) a
  munit P = Compose . munit (P :: P m) . PairWith . (, bot)
