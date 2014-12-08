module Lang.Lam.SyntaxHelpers where

import FP
import Lang.Lam.Syntax

infixl 9 @#
infixr 0 $#
infixr 6 /\#

int :: Int -> Exp
int = Fix . Lit . I

bool :: Bool -> Exp
bool = Fix . Lit . B

v :: String -> Exp
v = Fix . Var . Name

lam :: String -> Exp -> Exp
lam x = Fix . Lam (Name x)

add1 :: Exp -> Exp
add1 = Fix . Prim Add1

sub1 :: Exp -> Exp
sub1 = Fix . Prim Sub1

llet :: String -> Exp -> Exp -> Exp
llet n = Fix .: Let (Name n)

(@#) :: Exp -> Exp -> Exp
(@#) = Fix .: App

($#) :: Exp -> Exp -> Exp
($#) = (@#)

iif :: Exp -> Exp -> Exp -> Exp
iif = Fix ..: If

gez :: Exp -> Exp
gez = Fix . Prim IsNonNeg

(/\#) :: Exp -> Exp -> Exp
e1 /\# e2 = iif e1 e2 $ bool False

someBool :: Exp
someBool = gez $ add1 $ int 0

