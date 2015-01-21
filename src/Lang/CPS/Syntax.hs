module Lang.CPS.Syntax where

import FP
import Lang.Common

data PrePico n =
    Lit Lit
  | Var n
  deriving (Eq, Ord)
type SGPico = PrePico SGName

data PreAtom n c =
    Pico (PrePico n)
  | Prim Op (PrePico n)
  | LamF n n c
  | LamK n c
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreAtom n c) where pcompare = discreteOrder
type SPreAtom n c = Stamped LocNum (PreAtom n c)
type Atom n = SPreAtom n (Call n)
type SGAtom = Atom SGName

data PreCall n c =
    Let n (SPreAtom n c) c
  | If (PrePico n) c c 
  | AppF (PrePico n) (PrePico n) (PrePico n)
  | AppK (PrePico n) (PrePico n)
  | Halt (PrePico n)
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreCall n c) where pcompare = discreteOrder
type Call n = StampedFix LocNum (PreCall n)
type SGCall = Call SGName
makePrisms ''PreCall

freeVarsLam :: [SGName] -> PreCall SGName SGCall -> Set SGName
freeVarsLam xs c = freeVarsCall c \-\ toSet xs

freeVarsPico :: SGPico -> Set SGName
freeVarsPico (Lit _) = bot
freeVarsPico (Var x) = singleton x

freeVarsAtom :: PreAtom SGName SGCall -> Set SGName
freeVarsAtom (Pico p) = freeVarsPico p
freeVarsAtom (Prim _ ax) = freeVarsPico ax
freeVarsAtom (LamF x kx c) = freeVarsLam [x, kx] $ stampedFix c
freeVarsAtom (LamK x c) = freeVarsLam [x] $ stampedFix c

freeVarsCall :: PreCall SGName SGCall -> Set SGName
freeVarsCall (Let x a c) = freeVarsAtom (stamped a) \/ (freeVarsCall (stampedFix c) \-\ singleton x)
freeVarsCall (If ax tc fc) = freeVarsPico ax \/ joins (freeVarsCall . stampedFix ^$ [tc, fc])
freeVarsCall (AppF fx ax kx) = joins $ freeVarsPico ^$ [fx, ax, kx]
freeVarsCall (AppK kx ax) = joins $ freeVarsPico ^$ [kx, ax]
freeVarsCall (Halt ax) = freeVarsPico ax
