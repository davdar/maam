module MAAM.M.Delta where

import MAAM.M.Syntax
import MAAM.Common
import MAAM.Classes
import FP

class Delta (val :: * -> *) δ | δ -> val where
  lit :: P δ -> Lit -> val μ
  clo :: P δ -> [Name] -> Call -> Env addr time μ -> val μ
  op :: P δ -> Op -> val μ -> Set (val μ)
  elimBool :: P δ -> val μ -> Set Bool
  elimClo :: (AAM addr time μ) => P δ -> val μ -> Set ([Name], Call, Env addr time μ)

elimBoolM :: (Delta val δ, MonadZero m, MonadPlus m) => P δ -> val μ -> m Bool
elimBoolM = msum .: elimBool

elimCloM :: (AAM addr time μ, Delta val δ, MonadZero m, MonadPlus m, Ord addr) => P δ -> val μ -> m ([Name], Call, Env addr time μ)
elimCloM = msum .: elimClo

type Env addr time μ = Map Name addr
-- data E μ = E μ
-- type instance Cell (E μ) = Env μ

type Store val δ addr time μ = Map addr (Set (val μ))
-- data S δ μ = S δ μ
-- type instance Cell (S δ μ) = Store δ μ
