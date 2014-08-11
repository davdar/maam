module MAAM.Classes.Time where

import FP

class Time (τ :: * -> *) where
  tzero :: τ σ
  tick :: σ -> τ σ -> τ σ

timeP :: P τ -> P σ -> P (τ σ)
timeP P P = P

