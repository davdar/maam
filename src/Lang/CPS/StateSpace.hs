module Lang.CPS.StateSpace where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.Common

data Addr lτ dτ (ψ :: *) = Addr
  { addrLocation :: SGName
  , addrLexicalTime :: lτ ψ
  , addrDynamicTime :: dτ ψ
  } deriving (Eq, Ord)

type Env lτ dτ ψ = Map SGName (Addr lτ dτ ψ)
type Store val lτ dτ ψ = Map (Addr lτ dτ ψ) (val lτ dτ ψ)

data 𝒮 val lτ dτ ψ = 𝒮
  { 𝓈lτ :: lτ ψ
  , 𝓈dτ :: dτ ψ
  , 𝓈ρ :: Env lτ dτ ψ
  , 𝓈σ :: Store val lτ dτ ψ
  } deriving (Eq, Ord)
makeLenses ''𝒮
instance (Initial (lτ ψ), Initial (dτ ψ)) => Initial (𝒮 val lτ dτ ψ) where
  initial = 𝒮 initial initial initial initial

data Clo lτ dτ ψ = Clo 
  { cloLoc :: LocNum
  , cloArgs :: [SGName]
  , cloCall :: SGCall
  , cloEnv :: Env lτ dτ ψ
  , cloTime :: lτ ψ
  } deriving (Eq, Ord)

class Val lτ dτ ψ val | val -> lτ, val -> dτ, val -> ψ where
  lit :: Lit -> val 
  clo :: Clo lτ dτ ψ -> val 
  binop :: BinOp -> val -> val -> val
  elimBool :: val -> Set Bool
  elimClo :: val -> Set (Clo lτ dτ ψ)
