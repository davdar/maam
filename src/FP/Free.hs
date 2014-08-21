module FP.Free where

import FP.Core

infixr 6 :++:
infixr 6 :+++:

-- FreeMonoid {{{

data FreeMonoid a = MonoidElem a | Null | FreeMonoid a :++: FreeMonoid a
instance Unit FreeMonoid where
  unit = MonoidElem
instance Monoid (FreeMonoid a) where
  null = Null
  (++) = (:++:)

-- }}}

-- FreeFunctor {{{

data FreeFunctor f a = FunctorElem a | Apply (f (FreeFunctor f a))
instance Unit (FreeFunctor f) where
  unit = FunctorElem

-- }}}

-- FreeMonoidFunctor {{{

data FreeMonoidFunctor f a = 
    MonoidFunctorElem a 
  | MFNull 
  | FreeMonoidFunctor f a :+++: FreeMonoidFunctor f a  
  | MFApply (f (FreeMonoidFunctor f a))
instance Unit (FreeMonoidFunctor f) where
  unit = MonoidFunctorElem
instance Monoid (FreeMonoidFunctor f a) where
  null = MFNull
  (++) = (:+++:)

-- }}}


