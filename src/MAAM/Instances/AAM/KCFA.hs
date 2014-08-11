module MAAM.Instances.AAM.KCFA where

import FP
import MAAM.Common
import MAAM.Classes.AAM

data Kμ = Kμ Int
kμ :: P Kμ
kμ = P

data KAddr σ = KAddr
  { cName :: Name
  , cTime :: [σ]
  }

instance AAM Kμ where
  type Time Kμ = []
  type Addr Kμ σ = (Name, [σ])
  tzero :: Kμ -> Time Kμ σ
  tzero _ = []
  tick :: Kμ -> σ -> Time Kμ σ -> Time Kμ σ
  tick (Kμ k) = firstN k .: (:)
  alloc :: Kμ -> Name -> Time Kμ σ -> Addr Kμ σ
  alloc _ = (,)
