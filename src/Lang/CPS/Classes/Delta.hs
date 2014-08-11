module Lang.CPS.Classes.Delta where

import FP
import MAAM

import Lang.CPS.Syntax

newtype Env μ = Env { runEnv :: Map Name (Addr μ) }
  deriving (Eq, Ord)
envP :: P μ -> P (Env μ)
envP P = P
envL :: P μ -> Lens (Env μ) (Map Name (Addr μ))
envL P = isoLens runEnv Env

newtype Store δ μ = Store { runStore :: Map (Addr μ) (Val δ μ) }
deriving instance (Eq (Addr μ), Eq (Val δ μ)) => Eq (Store δ μ)
deriving instance (Ord (Addr μ), Ord (Val δ μ)) => Ord (Store δ μ)
storeP :: P δ -> P μ -> P (Store δ μ)
storeP P P = P
storeL :: P δ -> P μ -> Lens (Store δ μ) (Map (Addr μ) (Val δ μ))
storeL P P = isoLens runStore Store

type Σ δ μ = (Call, Env μ, Store δ μ)
σ :: P δ -> P μ -> P (Σ δ μ)
σ P P = P

data Clo μ = Clo 
  { cloArgs :: [Name]
  , cloCall :: Call
  , cloEnv :: Env μ
  } deriving (Eq, Ord)

class Delta δ where
  type Val δ :: * -> *
  type Δ δ μ :: Constraint
  lit :: (Δ δ μ) => P δ -> Lit -> Val δ μ
  clo :: (Δ δ μ) => P δ -> Clo μ -> Val δ μ
  op :: (Δ δ μ) => P δ -> Op -> Val δ μ -> Val δ μ
  elimBool :: (Δ δ μ) => P δ -> Val δ μ -> Set Bool
  elimClo :: (Δ δ μ) => P δ -> Val δ μ -> Set (Clo μ)
