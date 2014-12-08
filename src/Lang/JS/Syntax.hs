module Lang.JS.Syntax where

import FP
import qualified FP.Pretty as P

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

instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b
  pretty UndefinedL = P.con "ᴜɴᴅᴇғɪɴᴇᴅ"
  pretty NullL = P.con "ɴᴜʟʟ"
  pretty (S s) = pretty $ "\"" ++ s ++ "\""

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

instance Pretty Name where
  pretty (Name s) = P.bdr s
instance Pretty LocNum where
  pretty (LocNum i) = P.pun $ ptoString i
instance Pretty GName where
  pretty (GName iM s) = exec
    [ pretty s
    , maybeElimOn iM (return ()) $ \ i -> exec [P.pun "#", P.pun $ toString i]
    ]
instance Pretty BdrNum where
  pretty (BdrNum i) = P.format (P.setFG 2) $ P.text $ ptoString i
instance (Pretty n, Pretty e) => Pretty (PreExp n e) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  -- pretty (Lam n e) = P.parensIfWrapped $ P.nest 2 $ P.hvsep
  --   [ exec [P.hsep [P.key "λ", P.pretty n], P.pun "."]
  --   , pretty e
  --   ]
  -- pretty (Prim o e) = P.app [pretty o, pretty e]
  -- pretty (Let n e b) = P.parensIfWrapped $ P.hvsep
  --   [ P.hsep [P.key "let", pretty n, P.keyPun ":=", P.hvsep [P.nest 2 $ pretty e, P.key "in"]]
  --   , P.hsep [pretty b]
  --   ]
  -- pretty (App fe e) = P.app [pretty fe, pretty e]
  -- pretty (If e te fe) = P.parensIfWrapped $ P.nest 2 $ P.hvsep $ map (P.nest 2)
  --   [ P.hsep [P.key "if", pretty e]
  --   , P.hvsep [P.key "then", pretty te]
  --   , P.hvsep [P.key "else", pretty fe]
  --   ]
instance (Pretty n) => Functorial Pretty (PreExp n) where
  functorial = W
