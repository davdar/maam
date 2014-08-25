module Lang.Lam.Syntax where

import FP

newtype Name = Name { getName :: String }
  deriving (Eq, Ord)
data GName = GName
  { gnameMark :: Maybe Int
  , gname :: Name
  }
  deriving (Eq, Ord)
type SName = Stamped Int Name
type SGName = Stamped Int GName

data Lit = I Int | B Bool
  deriving (Eq, Ord)
instance PartialOrder Lit where pcompare = discreteOrder
coerceI :: Lit -> Maybe Int
coerceI (I i) = Just i
coerceI _ = Nothing
coerceB :: Lit -> Maybe Bool
coerceB (B b) = Just b
coerceB _ = Nothing

data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance PartialOrder Op where pcompare = discreteOrder

data PreExp n e = 
    Lit Lit
  | Var n
  | Lam n e
  | Prim Op e
  | App e e
  | If e e e
  deriving (Eq, Ord)
type Exp n = Fix (PreExp n)
type StampedExp n = StampedFix Int (PreExp n)
