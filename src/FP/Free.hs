module FP.Free where

import FP.Core

infixr 6 :++:
infixr 6 :+++:

data FreeMonoid a = MonoidElem a | Null | FreeMonoid a :++: FreeMonoid a
instance Unit FreeMonoid where
  unit = MonoidElem
instance Monoid (FreeMonoid a) where
  null = Null
  (++) = (:++:)
instance Functor FreeMonoid where
  map :: (a -> b) -> FreeMonoid a -> FreeMonoid b
  map f (MonoidElem a) = MonoidElem $ f a
  map _ Null = Null
  map f (x1 :++: x2) = map f x1 :++: map f x2

data FreeFunctor f a = FunctorElem a | Apply (f (FreeFunctor f a))
instance Unit (FreeFunctor f) where
  unit = FunctorElem
instance (Functor f) => Functor (FreeFunctor f) where
  map :: (a -> b) -> FreeFunctor f a -> FreeFunctor f b
  map f (FunctorElem a) = FunctorElem $ f a
  map f (Apply aF) = Apply $ map (map f) aF

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
instance (Functor f) => Functor (FreeMonoidFunctor f) where
  map :: (a -> b) -> FreeMonoidFunctor f a -> FreeMonoidFunctor f b
  map f (MonoidFunctorElem a) = MonoidFunctorElem $ f a
  map _ MFNull = MFNull
  map f (x1 :+++: x2) = map f x1 :+++: map f x2
  map f (MFApply aF) = MFApply $ map (map f) aF
