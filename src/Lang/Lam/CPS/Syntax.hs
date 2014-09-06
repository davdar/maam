module Lang.Lam.CPS.Syntax where

import FP
import Lang.Lam.Syntax (SGName, LocNum, Op, Lit)

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
type Call n = StampedFix LocNum (PreCall n)
type SGCall = Call SGName

isAppF :: SGCall -> Bool
isAppF (StampedFix _ (AppF _ _ _)) = True
isAppF _ = False
