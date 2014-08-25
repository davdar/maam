module Lang.CPS.Syntax.AST where

import FP

type Name = String
data SName = SName 
  { snameMark :: Maybe Int
  , snameName :: Name 
  }
  deriving (Eq, Ord)
sname :: Name -> SName
sname = SName Nothing

data RName = RName
  { rNameID :: Int
  , rName :: SName
  }
instance Eq RName where
  (==) = (==) `on` rNameID
instance Ord RName where
  compare = compare `on` rNameID

data Lit = I Int | B Bool
  deriving (Eq, Ord)
coerceI :: Lit -> Maybe Int
coerceI (I i) = Just i
coerceI _ = Nothing
coerceB :: Lit -> Maybe Bool
coerceB (B b) = Just b
coerceB _ = Nothing

instance PartialOrder Lit where pcompare = discreteOrder
data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance PartialOrder Op where pcompare = discreteOrder
type SAtom = Atom SName SCall
type RAtom = Atom RName RCall
data Atom n c =
    Lit Lit
  | Var n
  | Prim Op (Atom n c)
  | Lam [n] c
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (Atom n c) where pcompare = discreteOrder
type SCall = Fix (Call SName)
data RCall = RCall 
  { rCallID :: Int
  , rCall :: Call RName RCall
  }
instance Eq RCall where
  (==) = (==) `on` rCallID
instance Ord RCall where
  compare = compare `on` rCallID
data Call n c =
    If (Atom n c) c c 
  | App (Atom n c) [Atom n c]
  | Halt (Atom n c)

-- Smart Constructors {{{

letAtom :: String -> SAtom -> SCall -> SCall
letAtom x a c = Fix $ App (Lam [sname x] c) [a]

letApp :: String -> SAtom -> SAtom -> SCall -> SCall
letApp x f a c = Fix $ App f [a, Lam [sname x] c]

lam :: String -> String -> SCall -> SAtom
lam x k c = Lam [sname x, sname k] c

(@#) :: SAtom -> SAtom -> SCall
k @# x = Fix $ App k [x]

(@@#) :: SAtom -> [SAtom] -> SCall
(@@#) = Fix .: App

v :: String -> SAtom
v = Var . sname

true :: SAtom
true = Lit $ B True

false :: SAtom
false = Lit $ B False

int :: Int -> SAtom
int = Lit . I

halt :: SAtom -> SCall
halt = Fix . Halt

ifc :: SAtom -> SCall -> SCall -> SCall
ifc = Fix ..: If

-- }}}

