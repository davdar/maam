module MAAM.Classes.AAM where

import FP
import MAAM.Common

class AAM μ where
  type Time μ :: * -> *
  type Addr μ σ :: *
  tzero :: μ -> Time μ σ
  tick :: μ -> σ -> Time μ σ -> Time μ σ
  alloc :: μ -> Name -> Time μ σ -> Addr μ σ

timeP :: P μ -> P σ -> P (Time μ σ)
timeP P P = P
