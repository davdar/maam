module Lang.CPS.Classes.Delta where

import FP
import MAAM

import Lang.CPS.Syntax

type Ψ = Call
ψ :: P Ψ
ψ = P


data Addr μ = Addr
  { addrLocation :: Name
  , addrLexicalTime :: LexicalTime μ Ψ
  , addrDynamicTime :: DynamicTime μ Ψ
  }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (Addr μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (Addr μ)

newtype Env μ = Env { runEnv :: Map Name (Addr μ) }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (Env μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (Env μ)
deriving instance HasBot (Env μ)
envP :: μ -> P (Env μ)
envP _ = P
envL :: μ -> Lens (Env μ) (Map Name (Addr μ))
envL _ = isoLens runEnv Env

newtype Store δ μ = Store { runStore :: Map (Addr μ) (Val δ μ) }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ), Eq (Val δ μ)) => Eq (Store δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), Ord (Val δ μ)) => Ord (Store δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), PartialOrder (Val δ μ)) => PartialOrder (Store δ μ)
deriving instance HasBot (Store δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => JoinLattice (Store δ μ)
storeP :: P δ -> μ -> P (Store δ μ)
storeP P _ = P
storeL :: P δ -> μ -> Lens (Store δ μ) (Map (Addr μ) (Val δ μ))
storeL P _ = isoLens runStore Store

data Clo μ = Clo 
  { cloArgs :: [Name]
  , cloCall :: Call
  , cloEnv :: Env μ
  , cloTime :: LexicalTime μ Ψ
  } 
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (Clo μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (Clo μ)

class Delta δ where
  type Val δ :: * -> *
  type Δ δ μ :: Constraint
  lit :: (Δ δ μ) => P δ -> Lit -> Val δ μ
  clo :: (Δ δ μ) => P δ -> Clo μ -> Val δ μ
  op :: (Δ δ μ) => P δ -> Op -> Val δ μ -> Val δ μ
  elimBool :: (Δ δ μ) => P δ -> Val δ μ -> Set Bool
  elimClo :: (Δ δ μ) => P δ -> Val δ μ -> Set (Clo μ)
