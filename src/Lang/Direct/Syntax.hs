module Lang.Direct.Syntax where

import FP

type Name = String

data Lit = I Int | B Bool
  deriving (Eq, Ord)
data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
data Exp = 
    Lit Lit
  | Var Name
  | Lam [Name] Exp
  | Prim Op Exp
  | App Exp [Exp]
  | If Exp Exp Exp
  deriving (Eq, Ord)
