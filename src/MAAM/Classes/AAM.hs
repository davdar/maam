module MAAM.Classes.AAM where

import FP
import MAAM.Common

class AAM μ where
  type Addr μ :: *
  type Time μ :: * -> *
  tzero :: P μ -> Time μ σ
  tick :: P μ -> σ -> Time μ σ -> Time μ σ
  alloc :: P μ -> Name -> Time μ σ -> Addr μ

time :: P μ -> P σ -> P (Time μ σ)
time P P = P
