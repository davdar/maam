module Lang.Lam.CPS.Classes.Delta where

import FP
import MAAM
import Lang.Lam.CPS.Syntax
import qualified FP.Pretty as P
import Lang.Lam.CPS.Instances.PrettySyntax
import Lang.Lam.Syntax (SGName, Lit(..), Op(..))

type Ψ = Int
ψ :: P Ψ
ψ = P

data Addr μ = Addr
  { addrLocation :: SGName
  , addrLexicalTime :: LexicalTime μ Ψ
  , addrDynamicTime :: DynamicTime μ Ψ
  }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (Addr μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (Addr μ)
instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (Addr μ) where
  pretty (Addr loc lτ dτ) = P.collection "<" ">" "," [pretty loc, pretty lτ, pretty dτ]

newtype Env μ = Env { runEnv :: Map SGName (Addr μ) }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (Env μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (Env μ)
deriving instance HasBot (Env μ)
deriving instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (Env μ)
envP :: μ -> P (Env μ)
envP _ = P
envL :: μ -> Lens (Env μ) (Map SGName (Addr μ))
envL _ = isoLens runEnv Env

newtype Store δ μ = Store { runStore :: Map (Addr μ) (Val δ μ) }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ), Eq (Val δ μ)) => Eq (Store δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), Ord (Val δ μ)) => Ord (Store δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), PartialOrder (Val δ μ)) => PartialOrder (Store δ μ)
deriving instance HasBot (Store δ μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ), JoinLattice (Val δ μ)) => JoinLattice (Store δ μ)
deriving instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ), Pretty (Val δ μ)) => Pretty (Store δ μ)
storeP :: P δ -> μ -> P (Store δ μ)
storeP P _ = P
storeL :: P δ -> μ -> Lens (Store δ μ) (Map (Addr μ) (Val δ μ))
storeL P _ = isoLens runStore Store

data Clo μ = Clo 
  { cloArgs :: [SGName]
  , cloCall :: Call SGName
  , cloEnv :: Env μ
  , cloTime :: LexicalTime μ Ψ
  } 
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (Clo μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (Clo μ)
instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (Clo μ) where
  pretty (Clo xs c ρ lτ) = P.collection "<" ">" "," [pretty $ prettyLam xs c, pretty ρ, pretty lτ]

class Delta δ where
  type Val δ :: * -> *
  type Δ δ μ :: Constraint
  lit :: (Δ δ μ) => P δ -> Lit -> Val δ μ
  clo :: (Δ δ μ) => P δ -> Clo μ -> Val δ μ
  op :: (Δ δ μ) => P δ -> Op -> Val δ μ -> Val δ μ
  elimBool :: (Δ δ μ) => P δ -> Val δ μ -> Set Bool
  elimClo :: (Δ δ μ) => P δ -> Val δ μ -> Set (Clo μ)
