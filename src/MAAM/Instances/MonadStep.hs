module MAAM.Instances.MonadStep where

import FP
import MAAM.Classes.MonadStep

instance (MonadStep m, Functorial JoinLattice m) => MonadStep (ListSetT m) where
  type SS (ListSetT m) = SS m :.: Set
  type SSC (ListSetT m) a = (SSC m (Set a), Ord a)
  mstep :: (SSC (ListSetT m) a, SSC (ListSetT m) b) => (a -> ListSetT m b) -> (SS (ListSetT m) a -> SS (ListSetT m) b)
  mstep f = Compose . mstep (mmap sset . runListSetT . msums . map f . toList) . runCompose
  mstepUnit :: (SSC (ListSetT m) a) => P (ListSetT m) -> a -> SS (ListSetT m) a
  mstepUnit P = Compose . mstepUnit (P :: P m) . ssingleton

newtype PairWith s a = PairWith { runPairWith :: (a, s) }
instance (MonadStep m, JoinLattice s) => MonadStep (StateT s m) where
  type SS (StateT s m) = SS m :.: PairWith s
  type SSC (StateT s m) a = (SSC m (PairWith s a))
  mstep :: (SSC (StateT s m) a, SSC (StateT s m) b) => (a -> StateT s m b) -> (SS (StateT s m) a -> SS (StateT s m) b)
  mstep f = Compose . mstep (\ (PairWith (a, s)) -> map PairWith $ unStateT (f a) s) . runCompose
  mstepUnit :: (SSC (StateT s m) a) => P (StateT s m) -> a -> SS (StateT s m) a
  mstepUnit P = Compose . mstepUnit (P :: P m) . PairWith . (,bot)
