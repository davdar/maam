module MAAM.Classes.MonadStep where

import FP

class (Monad m, Unit (SS m)) => MonadStep m where
  type SS m :: * -> *
  mstep :: (a -> m b) -> SS m a -> SS m b

-- class (CMonad c m, CUnit c (CSS m)) => CMonadStep c m | m -> c where
--   type CSS m :: * -> *
--   cmstep :: (c a, c b) => (a -> m b) -> CSS m a -> CSS m b
