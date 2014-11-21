module MAAM.Instances.MonadStep where

import FP
import MAAM.Classes.MonadStep

-- Identity
instance MonadStep ID ID where
  mstepγ :: (a -> ID b) -> (ID a -> ID b)
  mstepγ = extend

-- State
instance (MonadStep ς m, Functor m) => MonadStep (ς :.: (,) 𝓈) (StateT 𝓈 m) where
  mstepγ :: (a -> StateT 𝓈 m b) -> ((ς :.: (,) 𝓈) a -> (ς :.: (,) 𝓈)  b)
  mstepγ f = onComposeIso $ mstepγ $ \ (s, a) -> swap ^$ unStateT (f a) s

-- Flow Insensitive
instance (MonadStep ς m, Functorial JoinLattice m) => MonadStep (ς :.: Set) (SetT m) where
  mstepγ :: (a -> SetT m b) -> (ς :.: Set) a -> (ς :.: Set) b
  mstepγ f = onComposeIso $ mstepγ $ runSetT . msum . map f . toList

-- Flow Sensitive
instance (MonadStep ς m, Functorial JoinLattice m, Commute ς Set) => MonadStep (Set :.: ς) (SetT m) where
  mstepγ :: (a -> SetT m b) -> (Set :.: ς) a -> (Set :.: ς) b
  mstepγ f = onComposeIso $ extend $ commute . mstepγ (runSetT . f)
