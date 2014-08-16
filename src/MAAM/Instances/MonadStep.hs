module MAAM.Instances.MonadStep where

import FP
import MAAM.Classes.MonadStep

instance MonadStep ID where
  type SS ID a = a
  type SSC ID a = ()
  mstep :: (SSC ID a, SSC ID b) => (a -> ID b) -> (SS ID a -> SS ID b)
  mstep f = runID . f
  munit :: (SSC ID a) => P ID -> a -> SS ID a
  munit P = id

instance (MonadStep m, Functorial JoinLattice m) => MonadStep (ListSetT m) where
  type SS (ListSetT m) a = SS m (Set a)
  type SSC (ListSetT m) a = (SSC m (Set a), Ord a)
  mstep :: forall a b. (SSC (ListSetT m) a, SSC (ListSetT m) b) => (a -> ListSetT m b) -> (SS (ListSetT m) a -> SS (ListSetT m) b)
  mstep f = 
    (mstep :: (Set a -> m (Set b)) -> (SS m (Set a) -> SS m (Set b))) 
    $ mmap sset . runListSetT . msums . map f . toList
  munit :: forall a. (SSC (ListSetT m) a) => P (ListSetT m) -> a -> SS (ListSetT m) a
  munit P = 
    (munit (P :: P m) :: Set a -> SS m (Set a))
    . ssingleton

newtype PairWith s a = PairWith { runPairWith :: (a, s) }
  deriving (Eq, Ord)
instance (MonadStep m, HasBot s) => MonadStep (StateT s m) where
  type SS (StateT s m) a = SS m (a, s)
  type SSC (StateT s m) a = SSC m (a, s)
  mstep :: forall a b. (SSC (StateT s m) a, SSC (StateT s m) b) => (a -> StateT s m b) -> (SS (StateT s m) a -> SS (StateT s m) b)
  mstep f = 
    (mstep :: ((a, s) -> m (b, s)) -> (SS m (a, s) -> SS m (b, s))) 
    $ \ (a, s) -> unStateT (f a) s
  munit :: forall a. (SSC (StateT s m) a) => P (StateT s m) -> a -> SS (StateT s m) a
  munit P =
    (munit (P :: P m) :: (a, s) -> SS m (a, s))
    . (, bot)
