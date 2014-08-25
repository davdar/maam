module MAAM.Classes.Temporal where

import FP

class (Functorial Eq (Time θ), Functorial Ord (Time θ), Functorial Pretty (Time θ)) => Temporal θ where
  type Time θ :: * -> *
  tzero :: P θ -> Time θ ψ
  tick :: θ -> ψ -> Time θ ψ -> Time θ ψ
