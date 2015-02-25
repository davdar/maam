module Lang.Common where

import FP
import qualified FP.Pretty as P

newtype Name = Name { getName :: String }
  deriving (Eq, Ord)
data GName = GName
  { gnameMark :: Maybe Int
  , gname :: Name
  }
  deriving (Eq, Ord)
newtype LocNum = LocNum Int deriving (Eq, Ord, PartialOrder, Peano)
newtype BdrNum = BdrNum Int deriving (Eq, Ord, PartialOrder, Peano)
type SName = Stamped BdrNum Name
type SGName = Stamped BdrNum GName
sgNameFromSName :: SName -> SGName
sgNameFromSName (Stamped i x) = Stamped i $ GName Nothing x

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

instance Pretty Name where
  pretty (Name s) = P.bdr s
instance Pretty LocNum where
  pretty (LocNum i) = P.pun $ ptoString i
instance Pretty BdrNum where
  pretty (BdrNum i) = P.format (P.setFG 2) $ P.text $ ptoString i
instance Pretty GName where
  pretty (GName iM s) = exec
    [ pretty s
    , elimMaybeOn iM (return ()) $ \ i -> exec [P.pun "#", P.pun $ toString i]
    ]
instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b
instance Pretty BinOp where
  pretty Add = P.key "+"
  pretty Sub = P.key "-"
  pretty GTE = P.key ">="

data VarLam n e = VarLam [n] e
instance (Pretty n, Pretty e) => Pretty (VarLam n e) where
  pretty (VarLam xs e) = P.atLevel 0 $ P.nest 2 $ P.hvsep
    [ P.hsep $ concat
      [ single $ P.key "λ"
      , map pretty xs
      , single $ P.pun "."
      ]
    , pretty e
    ]
