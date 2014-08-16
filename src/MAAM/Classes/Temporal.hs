module MAAM.Classes.Temporal where

import FP

class Temporal τ where
  type Time τ :: * -> *
  tzero :: P τ -> Time τ ψ
  tick :: τ -> ψ -> Time τ ψ -> Time τ ψ
