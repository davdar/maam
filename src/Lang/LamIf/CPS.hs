module Lang.LamIf.CPS where

import FP
import Lang.LamIf.Syntax hiding (PreExp(..))

data PrePico n =
    Lit Lit
  | Var n
  deriving (Eq, Ord)
type Pico = PrePico Name

data PreAtom n c =
    Pico (PrePico n)
  | Prim LBinOp (PrePico n) (PrePico n)
  | LamF n n c
  | LamK n c
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreAtom n c) where pcompare = discreteOrder
type Atom = Stamped LocNum (PreAtom Name Call)

data PreCall n c =
    Let n (Stamped LocNum (PreAtom n c)) c
  | If (PrePico n) c c 
  | AppF (PrePico n) (PrePico n) (PrePico n)
  | AppK (PrePico n) (PrePico n)
  | Halt (PrePico n)
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreCall n c) where pcompare = discreteOrder
type Call = StampedFix LocNum (PreCall Name)
makePrisms ''PreCall

freeVarsLam :: [Name] -> PreCall Name Call -> Set Name
freeVarsLam xs c = freeVarsCall c \-\ toSet xs

freeVarsPico :: Pico -> Set Name
freeVarsPico (Lit _) = bot
freeVarsPico (Var x) = singleton x

freeVarsAtom :: PreAtom Name Call -> Set Name
freeVarsAtom (Pico p) = freeVarsPico p
freeVarsAtom (Prim _ a1 a2) = freeVarsPico a1 \/ freeVarsPico a2
freeVarsAtom (LamF x kx c) = freeVarsLam [x, kx] $ stampedFix c
freeVarsAtom (LamK x c) = freeVarsLam [x] $ stampedFix c

freeVarsCall :: PreCall Name Call -> Set Name
freeVarsCall (Let x a c) = freeVarsAtom (stamped a) \/ (freeVarsCall (stampedFix c) \-\ singleton x)
freeVarsCall (If ax tc fc) = freeVarsPico ax \/ joins (freeVarsCall . stampedFix ^$ [tc, fc])
freeVarsCall (AppF fx ax kx) = joins $ freeVarsPico ^$ [fx, ax, kx]
freeVarsCall (AppK kx ax) = joins $ freeVarsPico ^$ [kx, ax]
freeVarsCall (Halt ax) = freeVarsPico ax
