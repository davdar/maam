module Lang.Lam.CPS.Classes.Val where

import FP
import Lang.Lam.CPS.Syntax
import qualified FP.Pretty as P
import Lang.Lam.CPS.Instances.PrettySyntax ()
import Lang.Lam.Syntax (SGName, Lit(..), Op(..), LocNum)

data Addr lτ dτ = Addr
  { addrLocation :: SGName
  , addrLexicalTime :: lτ
  , addrDynamicTime :: dτ
  } deriving (Eq, Ord)

newtype Env lτ dτ = Env { runEnv :: Map SGName (Addr lτ dτ) }
  deriving (Eq, Ord, Pretty)

newtype Store val lτ dτ = Store { runStore :: Map (Addr lτ dτ) (val lτ dτ) }
  deriving (Eq, Ord, PartialOrder, JoinLattice, Pretty)

data Clo lτ dτ = Clo 
  { cloLoc :: LocNum
  , cloArgs :: [SGName]
  , cloCall :: SGCall
  , cloEnv :: Env lτ dτ
  , cloTime :: lτ
  } deriving (Eq, Ord)

class Val val where
  lit :: (Ord lτ, Ord dτ) => Lit -> val lτ dτ
  clo :: (Ord lτ, Ord dτ) => Clo lτ dτ -> val lτ dτ
  op :: (Ord lτ, Ord dτ) => Op -> val lτ dτ -> val lτ dτ
  elimBool :: (Ord lτ, Ord dτ) => val lτ dτ -> Set Bool
  elimClo :: (Ord lτ, Ord dτ) => val lτ dτ -> Set (Clo lτ dτ)

instance (Pretty lτ, Pretty dτ) => Pretty (Addr lτ dτ) where
  pretty (Addr loc lτ dτ) = P.collection "<" ">" "," 
    [ exec [P.pun "x=", P.align $ pretty loc]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    , exec [P.pun "dτ=", P.align $ pretty dτ]
    ]

instance (Pretty lτ, Pretty dτ) => Pretty (Clo lτ dτ) where
  pretty (Clo l _xs _c _ρ lτ) = P.collection "<" ">" "," 
    [ exec [P.pun "λ=", pretty l]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    ]

