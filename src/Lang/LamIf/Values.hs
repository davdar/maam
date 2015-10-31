module Lang.LamIf.Values where

import FP
import Lang.LamIf.Stamp
import Lang.LamIf.Syntax

data Moment = Moment
  { call ∷ [Exp]
  , obj ∷ [Exp]
  } deriving (Eq,Ord)
makeLenses ''Moment
makePrettyRecord ''Moment

data Time = Time
  { lexical ∷ Moment
  , dynamic ∷ Moment
  } deriving (Eq,Ord)
makeLenses ''Time
makePrettyRecord ''Time
instance POrd Time where (⊑⊒) = discretePO

time₀ ∷ Time
time₀ = Time (Moment null null) (Moment null null)

data VarAddr = VarAddr
  { varAddrName ∷ Name
  , varAddrTime ∷ Time
  } deriving (Eq,Ord)
makeLenses ''VarAddr
makePrettyRecord ''VarAddr
instance POrd VarAddr where (⊑⊒) = discretePO

data ExpAddr = ExpAddr
  { expAddrExp ∷ Exp
  , expAddrTime ∷ Time
  } deriving (Eq,Ord)
makeLenses ''ExpAddr
makePrettyRecord ''ExpAddr
instance POrd ExpAddr where (⊑⊒) = discretePO

type Env = Name ⇰ VarAddr

type Store val = VarAddr ⇰ val

data Closure = Closure
  { closureExp ∷ Exp
  , closureArg ∷ Name
  , closureBody ∷ Exp
  , closureEnv ∷ Env
  , closureTime ∷ Moment 
  } deriving (Eq,Ord)
makePrettyRecord ''Closure

data AtomVal = 
    AtomValInt ℤ
  | AtomValAddr VarAddr
  | AtomValClo Closure
  | AtomValOp Op AtomVal AtomVal
  deriving (Eq,Ord)
makePrettySum ''AtomVal

data Frame =
    IfH Exp Exp Env Moment
  | LetH Name Exp Env Moment
  | OpL Op Exp Env Moment
  | OpR AtomVal Op
  | AppL Exp Env Moment
  | AppR AtomVal
  deriving (Eq,Ord)
makePrettySum ''Frame

type KStore val = Maybe ExpAddr ⇰ val

class Val val where
  intI ∷ ℤ → val 
  isZeroE ∷ val → 𝒫 𝔹
  delZero ∷ val → val
  cloI ∷ Closure → val 
  cloE ∷ val → 𝒫 Closure
  frameI ∷ (Frame,Maybe ExpAddr) → val
  frameE ∷ val → 𝒫 (Frame,Maybe ExpAddr)
  δ ∷ Op → val → val → val
