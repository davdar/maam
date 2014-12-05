module Lang.JS.Syntax where

import FP

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

data Lit = I Int | B Bool | UndefinedL | NullL | S String
  deriving (Eq, Ord)
instance PartialOrder Lit where pcompare = discreteOrder
coerceI :: Lit -> Maybe Int
coerceI (I i) = Just i
coerceI _ = Nothing
coerceB :: Lit -> Maybe Bool
coerceB (B b) = Just b
coerceB _ = Nothing

-- data Op = Add1 | Sub1 | IsNonNeg
--   deriving (Eq, Ord)
-- instance PartialOrder Op where pcompare = discreteOrder

data PreExp n e =
    Lit Lit
  | Var n
  | Func n e
  | ObjE [(n, e)]
  -- | Prim Op e
  | Let n e e
  | App e e
  | FieldRef e e
  | FieldSet e e e
  | Delete e e
  -- | If e e e
  deriving (Eq, Ord)
type Exp = Fix (PreExp Name)
type SExp = StampedFix LocNum (PreExp SName)
