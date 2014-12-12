module Lang.JS.Syntax
  ( module Lang.JS.Syntax
  , module Lang.Common
  , module Language.LambdaJS.Syntax
  ) where

import FP
import qualified FP.Pretty as P
import Language.LambdaJS.Syntax (Op(..), Label, SourcePos)
import Lang.Common (Name(..))

instance Pretty SourcePos where pretty = const $ P.pun "𝓁"

data Lit = B Bool | UndefinedL | NullL | S String | N Double
  deriving (Eq, Ord)
makePrisms ''Lit
instance PartialOrder Lit where pcompare = discreteOrder
instance Pretty Lit where
  pretty (B b) = pretty b
  pretty UndefinedL = P.con "ᴜɴᴅᴇғɪɴᴇᴅ"
  pretty NullL = P.con "ɴᴜʟʟ"
  pretty (S s) = pretty $ "\"" ++ s ++ "\""
  pretty (N d) = pretty d

makePrettySum ''Op

data PreExp e =
    Lit Lit
  | Var Name
  | Func [Name] e
  | ObjE [(Name, e)]
  -- | Prim Op e
  | Let [(Name, e)] e
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
  | LabelE Label e
  | Break Label e
  | TryCatch e Name e
  | TryFinally e e
  | Throw e
    -- Fig 9. Primitive Operators
  | PrimOp Op [e]
  deriving (Eq, Ord)
makePrettySum ''PreExp
instance Functorial Pretty PreExp where functorial = W

type Exp = StampedFix SourcePos PreExp
