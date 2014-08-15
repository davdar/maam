module MAAM.Instances.Temporal where

import FP
import MAAM.Classes.Temporal

--------------
-- Concrete --
--------------

data Cτ = Cτ

instance Temporal Cτ where
  type Time Cτ = []
  tzero Cτ = []
  tick Cτ = (:)

----------------
-- Zero (k=0) --
----------------

data Zτ = Zτ

data Zero a = Zero

instance Temporal Zτ where
  type Time Zτ = Zero
  tzero Zτ = Zero
  tick Zτ = const id

------------------
-- Last-k-sites --
------------------

data Kτ = Kτ Int

instance Temporal Kτ where
  type Time Kτ = []
  tzero (Kτ _) = []
  tick (Kτ k) = firstN k .: (:)
