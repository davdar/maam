module Lang.Lam.Syntax where

import FP

infixl 9 @#
infixr 0 $#
infixr 6 /\#

newtype Name = Name { getName :: String }
  deriving (Eq, Ord)
data GName = GName
  { gnameMark :: Maybe Int
  , gname :: Name
  }
  deriving (Eq, Ord)
newtype LocNum = LocNum Int
  deriving (Eq, Ord, Peano)
newtype BdrNum = BdrNum Int
  deriving (Eq, Ord, Peano)
type SName = Stamped BdrNum Name
type SGName = Stamped BdrNum GName
sgNameFromSName :: SName -> SGName
sgNameFromSName (Stamped i x) = Stamped i $ GName Nothing x

data Lit = I Int | B Bool
  deriving (Eq, Ord)
instance PartialOrder Lit where pcompare = discreteOrder

iL :: Prism Lit Int
iL = Prism
  { coerce = \ l -> case l of
      I i -> Just i
      _ -> Nothing
  , inject = I
  }

bL :: Prism Lit Bool
bL = Prism
  { coerce = \ l -> case l of
      B b -> Just b
      _ -> Nothing
  , inject = B
  }

data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance PartialOrder Op where pcompare = discreteOrder

data PreExp n e = 
    Lit Lit
  | Var n
  | Lam n e
  | Prim Op e
  | Let n e e
  | App e e
  | If e e e
  deriving (Eq, Ord)
type Exp = Fix (PreExp Name)
type SExp = StampedFix LocNum (PreExp SName)

-- Construction Helpers {{{

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

-- }}}
