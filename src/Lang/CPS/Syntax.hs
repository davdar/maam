module Lang.CPS.Syntax where

import FP
import MAAM

data Lit = I Integer | B Bool
  deriving (Eq, Ord)
coerceI :: Lit -> Maybe Integer
coerceI (I i) = Just i
coerceI _ = Nothing
coerceB :: Lit -> Maybe Bool
coerceB (B b) = Just b
coerceB _ = Nothing

instance PartialOrder Lit where pcompare = discreteOrder
data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance PartialOrder Op where pcompare = discreteOrder
data Atom =
    LitA Lit
  | Var Name
  | Prim Op Atom
  | Lam [Name] Call
  deriving (Eq, Ord)
instance PartialOrder Atom where pcompare = discreteOrder
data Call =
    If Atom Call Call
  | App Atom [Atom]
  | Halt Atom
  deriving (Eq, Ord)
instance PartialOrder Call where pcompare = discreteOrder
