module MAAM.Classes.MonadStep where

import FP

class (Monad m) => MonadStep m where
  type SS m :: * -> *
  type SSC m a :: Constraint
  mstep :: (SSC m a, SSC m b) => (a -> m b) -> SS m a -> SS m b
  mstepUnit :: (SSC m a) => P m -> a -> SS m a
