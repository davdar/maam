module Lang.LamIf.StateSpace where

import FP
import Lang.LamIf.Syntax
import Lang.LamIf.CPS

data Addr lτ dτ = Addr
  { addrLocation :: Name
  , addrLexicalTime :: lτ
  , addrDynamicTime :: dτ
  } deriving (Eq, Ord)

type Env lτ dτ = Map Name (Addr lτ dτ)
type Store val lτ dτ = Map (Addr lτ dτ) val

data 𝒮Cxt lτ dτ = 𝒮Cxt
  { 𝓈Cxtlτ :: lτ
  , 𝓈Cxtdτ :: dτ
  , 𝓈Cxtρ :: Env lτ dτ
  } deriving (Eq, Ord)
makeLenses ''𝒮Cxt
instance (Bot lτ, Bot dτ) => Bot (𝒮Cxt lτ dτ) where bot = 𝒮Cxt bot bot bot

data 𝒮 val lτ dτ = 𝒮
  { 𝓈Cxt :: 𝒮Cxt lτ dτ
  , 𝓈σ :: Store val lτ dτ
  } deriving (Eq, Ord)
makeLenses ''𝒮
instance (Bot lτ, Bot dτ) => Bot (𝒮 val lτ dτ) where bot = 𝒮 bot bot

𝓈lτL :: Lens (𝒮 val lτ dτ) lτ
𝓈lτL = 𝓈CxtlτL <.> 𝓈CxtL

𝓈dτL :: Lens (𝒮 val lτ dτ) dτ
𝓈dτL = 𝓈CxtdτL <.> 𝓈CxtL

𝓈ρL :: Lens (𝒮 val lτ dτ) (Env lτ dτ)
𝓈ρL = 𝓈CxtρL <.> 𝓈CxtL

data Clo lτ dτ = Clo 
  { cloLoc :: LocNum
  , cloArgs :: [Name]
  , cloCall :: Call
  , cloEnv :: Env lτ dτ
  , cloTime :: lτ
  } deriving (Eq, Ord)

data PicoVal lτ dτ =
    LitPicoVal Lit
  | AddrPicoVal (Addr lτ dτ)
  deriving (Eq, Ord)

class Val lτ dτ val | val -> lτ, val -> dτ where
  lit :: Lit -> val 
  clo :: Clo lτ dτ -> val 
  binop :: BinOp -> val -> val -> val
  tup :: (PicoVal lτ dτ, PicoVal lτ dτ) -> val
  elimBool :: val -> Set Bool
  elimClo :: val -> Set (Clo lτ dτ)
  elimTup :: val -> Set (PicoVal lτ dτ, PicoVal lτ dτ)
