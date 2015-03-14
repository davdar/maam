module Lang.LamIf.StateSpace where

import FP
import Lang.LamIf.Syntax
import Lang.LamIf.CPS

data Addr lτ dτ (ψ :: *) = Addr
  { addrLocation :: Name
  , addrLexicalTime :: lτ ψ
  , addrDynamicTime :: dτ ψ
  } deriving (Eq, Ord)

type Env lτ dτ ψ = Map Name (Addr lτ dτ ψ)
type Store val lτ dτ ψ = Map (Addr lτ dτ ψ) (val lτ dτ ψ)

data 𝒮 val lτ dτ ψ = 𝒮
  { 𝓈lτ :: lτ ψ
  , 𝓈dτ :: dτ ψ
  , 𝓈ρ :: Env lτ dτ ψ
  , 𝓈σ :: Store val lτ dτ ψ
  } deriving (Eq, Ord)
makeLenses ''𝒮
instance (Bot (lτ ψ), Bot (dτ ψ)) => Bot (𝒮 val lτ dτ ψ) where
  bot = 𝒮 bot bot bot bot

data Clo lτ dτ ψ = Clo 
  { cloLoc :: LocNum
  , cloArgs :: [Name]
  , cloCall :: Call
  , cloEnv :: Env lτ dτ ψ
  , cloTime :: lτ ψ
  } deriving (Eq, Ord)

class Val lτ dτ ψ val | val -> lτ, val -> dτ, val -> ψ where
  lit :: Lit -> val 
  clo :: Clo lτ dτ ψ -> val 
  binop :: BinOp -> val -> val -> val
  elimBool :: val -> Set Bool
  elimClo :: val -> Set (Clo lτ dτ ψ)
