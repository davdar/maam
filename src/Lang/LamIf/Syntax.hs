module Lang.LamIf.Syntax where

import FP

newtype RawName = RawName { getRawName :: String }
  deriving (Eq, Ord)
type SRawName = Stamped BdrNum RawName
data GenName = GenName
  { genNameMark :: Maybe Int
  , genNameRawName :: RawName
  }
  deriving (Eq, Ord)
newtype LocNum = LocNum Int deriving (Eq, Ord, PartialOrder, Peano)
newtype BdrNum = BdrNum Int deriving (Eq, Ord, PartialOrder, Peano)
type Name = Stamped BdrNum GenName
srawNameToName :: SRawName -> Name
srawNameToName (Stamped i x) = Stamped i $ GenName Nothing x

data Lit = I Int | B Bool
  deriving (Eq, Ord)
instance PartialOrder Lit where pcompare = discreteOrder
makePrisms ''Lit

data BinOp = Add | Sub | GTE
  deriving (Eq, Ord)
instance PartialOrder BinOp where pcompare = discreteOrder
data LBinOp = LBinOp
  { lbinOpOp :: BinOp
  , lbinOpLevel :: Int
  } deriving (Eq, Ord)

data PreExp n e = 
    Lit Lit
  | Var n
  | Lam n e
  | Prim LBinOp e e
  | Let n e e
  | App e e
  | If e e e
  | Tup e e
  | Pi1 e
  | Pi2 e
  deriving (Eq, Ord)
type RawExp = Fix (PreExp RawName)
type Exp = StampedFix LocNum (PreExp SRawName)

