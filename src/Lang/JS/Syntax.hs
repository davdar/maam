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

data Lit = I Int | B Bool | UndefinedL | NullL | S String | D Double
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
  pretty (D d) = pretty d

data Op = Plus | Minus | Times | Divide | PostIncrement | PostDecrement
        | PreIncrement | PreDecrement | UnaryMinus
  deriving (Eq, Ord)
instance Pretty Op where
  pretty Plus = P.key "+"
  pretty Minus = P.key "-"
  pretty Times = P.key "*"
  pretty Divide = P.key "/"
  pretty PostIncrement = P.key "++"
  pretty PostDecrement = P.key "--"
  pretty PreIncrement = P.key "++"
  pretty PreDecrement = P.key "--"
  pretty UnaryMinus = P.key "-"


newtype Label = Label String
              deriving (Eq, Ord)

instance Pretty Label where
  pretty (Label s) = pretty s

data PreExp n ln e =
    Lit Lit
  | Var n
  | Func [n] e
  | ObjE [(n, e)]
  -- | Prim Op e
  | Let [(n, e)] e
  | App e [e]
  | FieldRef e e
  | FieldSet e e e
  | Delete e e
    -- Fig 2. Mutable References
  | RefSet e e
  | Ref e
  | DeRef e
    -- Fig 8. Control Operators
  | If e e e
  | Seq e e
  | While e e
  | LabelE ln e
  | Break ln e
  | TryCatch e n e
  | TryFinally e e
  | Throw e
    -- Fig 9. Primitive Operators
  | PrimOp Op [e]
  deriving (Eq, Ord)
type Exp = Fix (PreExp Name Label)
type SExp = StampedFix LocNum (PreExp SName Label)

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
instance (Pretty n, Pretty e, Pretty ln) => Pretty (PreExp n ln e) where
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
instance (Pretty n, Pretty ln) => Functorial Pretty (PreExp n ln) where
  functorial = W
