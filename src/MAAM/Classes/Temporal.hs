module MAAM.Classes.Temporal where

import FP

class (Functorial Eq τ, Functorial Ord τ, Functorial Pretty τ) => Temporal τ where
  tzero :: τ ψ
  tick :: ψ -> τ ψ -> τ ψ
