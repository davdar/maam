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
makePrisms ''Lit
instance PartialOrder Lit where pcompare = discreteOrder

instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b
  pretty UndefinedL = P.con "ᴜɴᴅᴇғɪɴᴇᴅ"
  pretty NullL = P.con "ɴᴜʟʟ"
  pretty (S s) = pretty $ "\"" ++ s ++ "\""
  pretty (D d) = pretty d

data Op
  = ONumPlus
  | OStrPlus
  | OMul | ODiv | OMod | OSub
  | OLt | OStrLt
  | OBAnd | OBOr | OBXOr | OBNot
  | OLShift | OSpRShift | OZfRShift
  | OStrictEq
  | OAbstractEq
  | OTypeof
  | OSurfaceTypeof
  | OPrimToNum
  | OPrimToStr
  | OPrimToBool
  | OIsPrim
  | OHasOwnProp
  | OToInteger | OToInt32 | OToUInt32
  | OPrint -- ^for Rhino
  | OStrContains | OStrSplitRegExp | OStrSplitStrExp -- ^for Regexes
  | OStrStartsWith -- ^for forin
  | OStrLen
  | OObjIterHasNext | OObjIterNext | OObjIterKey -- ^more forin
  | OObjCanDelete
  | OMathExp | OMathLog | OMathCos | OMathSin | OMathAbs | OMathPow
  | ORegExpMatch | ORegExpQuote
  deriving (Eq, Ord)

instance Pretty Op where
  pretty ONumPlus = P.key "+"
  pretty OStrPlus = P.key "+"
  pretty OMul     = P.key "*"
  pretty ODiv     = P.key "/"
  pretty OMod     = P.key "%"
  pretty OSub     = P.key "-"
  pretty OLt      = P.key "<"
  pretty OStrLt   = P.key "<"
  pretty OBAnd    = P.key "&"
  pretty OBOr     = P.key "|"
  pretty OBXOr    = P.key "^"
  pretty OBNot    = P.key "~"


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
