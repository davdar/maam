module MAAM.Instances.AAM.Concrete where

import FP
import MAAM.Common
import MAAM.Classes.AAM

data Cμ
cμ :: P Cμ
cμ = P

data CAddr σ = CAddr
  { cName :: Name
  , cTime :: [σ]
  }

instance AAM Cμ where
  type Time Cμ = []
  type Addr Cμ σ = (Name, [σ])
  tzero :: P Cμ -> Time Cμ σ
  tzero P = []
  tick :: P Cμ -> σ -> Time Cμ σ -> Time Cμ σ
  tick P = (:)
  alloc :: P Cμ -> Name -> Time Cμ σ -> Addr Cμ σ
  alloc P = (,)
