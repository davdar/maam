module MAAM.Classes.Temporal where

class Temporal τ where
  type Time τ :: * -> *
  tzero :: τ -> Time τ ψ
  tick :: τ -> ψ -> Time τ ψ -> Time τ ψ
