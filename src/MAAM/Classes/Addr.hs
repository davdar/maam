module MAAM.Classes.Addr where

import FP
import MAAM.Common

class Addr 𝓁 where
  alloc :: Name -> τ -> 𝓁 τ
