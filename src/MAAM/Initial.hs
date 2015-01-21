module MAAM.Initial where

import FP

class Initial a where
  initial :: a
class Inject ς where
  inj :: a -> ς a

instance Inject ID where
  inj = ID

instance (Initial 𝓈) => Inject ((,) 𝓈) where
  inj :: a -> (𝓈, a)
  inj = (initial,)

instance Inject ListSet where
  inj = fromList . single

instance (Inject t, Inject u) => Inject (t :.: u) where
  inj = Compose . inj . inj

instance Initial (Map k v) where
  initial = mapEmpty
