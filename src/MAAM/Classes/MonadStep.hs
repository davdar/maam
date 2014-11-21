module MAAM.Classes.MonadStep where

import FP

class (Bind m) => MonadStep ς m | m -> ς where
  mstepγ :: (a -> m b) -> ς a -> ς b
