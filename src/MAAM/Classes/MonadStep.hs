module MAAM.Classes.MonadStep where

import FP

class (Monad m, Unit (SS m)) => MonadStep m where
  type SS m :: * -> *
  mstep :: (a -> m b) -> SS m a -> SS m b
