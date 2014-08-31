module Lang.Lam.CPS.Syntax where

import FP
import Lang.Lam.Syntax

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
type Atom n = PreAtom n (Call n)
type SGAtom = Atom SGName
type StampedSGAtom = Stamped LocNum (Atom SGName)

data PreCall n c =
    Let n (PreAtom n c) c
  | If (PrePico n) c c 
  | AppF (PrePico n) (PrePico n) (PrePico n)
  | AppK (PrePico n) (PrePico n)
  | Halt (PrePico n)
type Call n = StampedFix LocNum (PreCall n)
type SGCall = Call SGName
