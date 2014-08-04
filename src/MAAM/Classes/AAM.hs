module MAAM.Classes.AAM where

import FP
import MAAM.Common

class AAM addr time μ | μ -> addr, μ -> time where
  tzero :: P μ -> P 𝓁 -> time 𝓁
  tick :: P μ -> P 𝓁 -> History 𝓁 -> time 𝓁 -> time 𝓁
  alloc :: P μ -> P 𝓁 -> Name -> time 𝓁 -> addr

-- data T μ 𝓁 = T μ 𝓁
-- type instance Cell (T μ 𝓁) = Time μ 𝓁
