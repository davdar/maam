module Lang.CPS.Classes.Delta where

import FP
import MAAM

import Lang.CPS.Syntax

data Addr μ ψ = Addr
  { addrLocation :: Name
  , addrLexicalTime :: LexicalTime μ ψ
  , addrDynamicTime :: DynamicTime μ ψ
  }
deriving instance (Eq (DynamicTime μ ψ), Eq (LexicalTime μ ψ)) => Eq (Addr μ ψ)
deriving instance (Ord (DynamicTime μ ψ), Ord (LexicalTime μ ψ)) => Ord (Addr μ ψ)

newtype Env μ ψ = Env { runEnv :: Map Name (Addr μ ψ) }
deriving instance (Eq (DynamicTime μ ψ), Eq (LexicalTime μ ψ)) => Eq (Env μ ψ)
deriving instance (Ord (DynamicTime μ ψ), Ord (LexicalTime μ ψ)) => Ord (Env μ ψ)
envP :: P μ -> P ψ -> P (Env μ ψ)
envP P P = P
envL :: P μ -> P ψ -> Lens (Env μ ψ) (Map Name (Addr μ ψ))
envL P P = isoLens runEnv Env

newtype Store δ μ ψ = Store { runStore :: Map (Addr μ ψ) (Val δ μ ψ) }
deriving instance (Eq (DynamicTime μ ψ), Eq (LexicalTime μ ψ), Eq (Val δ μ ψ)) => Eq (Store δ μ ψ)
deriving instance (Ord (DynamicTime μ ψ), Ord (LexicalTime μ ψ), Ord (Val δ μ ψ)) => Ord (Store δ μ ψ)
storeP :: P δ -> P μ -> P ψ -> P (Store δ μ ψ)
storeP P P P = P
storeL :: P δ -> P μ -> P ψ -> Lens (Store δ μ ψ) (Map (Addr μ ψ) (Val δ μ ψ))
storeL P P P = isoLens runStore Store

data Clo μ ψ = Clo 
  { cloArgs :: [Name]
  , cloCall :: Call
  , cloEnv :: Env μ ψ
  , cloTime :: LexicalTime μ ψ
  } 
deriving instance (Eq (DynamicTime μ ψ), Eq (LexicalTime μ ψ)) => Eq (Clo μ ψ)
deriving instance (Ord (DynamicTime μ ψ), Ord (LexicalTime μ ψ)) => Ord (Clo μ ψ)

class Delta δ where
  type Val δ :: * -> * -> *
  type Δ δ μ :: Constraint
  lit :: (Δ δ μ) => P δ -> Lit -> Val δ μ ψ
  clo :: (Δ δ μ) => P δ -> Clo μ ψ -> Val δ μ ψ
  op :: (Δ δ μ) => P δ -> Op -> Val δ μ ψ -> Val δ μ ψ
  elimBool :: (Δ δ μ) => P δ -> Val δ μ ψ -> Set Bool
  elimClo :: (Δ δ μ) => P δ -> Val δ μ ψ -> Set (Clo μ ψ)
