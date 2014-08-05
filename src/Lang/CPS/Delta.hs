module Lang.CPS.Delta where

import FP
import MAAM

import Lang.CPS.Syntax

class Delta δ where
  type Val δ :: * -> *
  lit :: P δ -> Lit -> Val δ μ
  clo :: P δ -> [Name] -> Call -> Env μ -> Val δ μ
  op :: P δ -> Op -> Val δ μ -> Set (Val δ μ)
  elimBool :: P δ -> Val δ μ -> Set Bool
  elimClo :: P δ -> Val δ μ -> Set ([Name], Call, Env μ)

newtype Env μ = Env { runEnv :: Map Name (Addr μ) }
envP :: P μ -> P (Env μ)
envP P = P
envL :: P μ -> Lens (Env μ) (Map Name (Addr μ))
envL P = isoLens runEnv Env

newtype Store δ μ = Store { runStore :: Map (Addr μ) (Set (Val δ μ)) }
storeP :: P δ -> P μ -> P (Store δ μ)
storeP P P = P
storeL :: P δ -> P μ -> Lens (Store δ μ) (Map (Addr μ) (Set (Val δ μ)))
storeL P P = isoLens runStore Store
