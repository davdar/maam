module Lang.Lam.CPS.Syntax where

import FP
import Lang.Lam.Syntax

data PreAtom n c =
    Lit Lit
  | Var n
  | Prim Op (PreAtom n c)
  | LamF n n c
  | LamK n c
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreAtom n c) where pcompare = discreteOrder
type Atom n = PreAtom n (Call n)
type SGAtom = Atom SGName

data PreCall n c =
    If (PreAtom n c) c c 
  | AppF (PreAtom n c) (PreAtom n c) (PreAtom n c)
  | AppK (PreAtom n c) (PreAtom n c)
  | Halt (PreAtom n c)
type Call n = StampedFix LocNum (PreCall n)
type SGCall = Call SGName
