module Lang.JS.Syntax where

import FP
import qualified FP.Pretty as P
import qualified Language.LambdaJS.Syntax as LJS
import qualified Language.ECMAScript3 as JS
import qualified Language.LambdaJS.Desugar as LJS
import qualified Language.LambdaJS.RemoveHOAS as LJS
import FP.DerivingPretty

data Lit = I Int | B Bool | UndefinedL | NullL | S String | D Double
  deriving (Eq, Ord)
makePrisms ''Lit
instance PartialOrder Lit where pcompare = discreteOrder

type Op = LJS.Op
makePrettySum ''LJS.Op

instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b
  pretty UndefinedL = P.con "ᴜɴᴅᴇғɪɴᴇᴅ"
  pretty NullL = P.con "ɴᴜʟʟ"
  pretty (S s) = pretty $ "\"" ++ s ++ "\""
  pretty (D d) = pretty d

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
makePrettySum ''PreExp

type Exp = StampedFix JS.SourcePos (PreExp String LJS.Label)
instance Pretty LJS.SourcePos where pretty = P.pun . show

instance (Pretty n, Pretty ln) => Functorial Pretty (PreExp n ln) where
  functorial = W

convert :: LJS.ExprPos -> Exp
convert = \ case
  LJS.ENumber sp n -> StampedFix sp $ Lit $ D n
  LJS.EString sp s -> StampedFix sp $ Lit $ S $ fromChars s
  LJS.EBool sp b -> StampedFix sp $ Lit $ B b
  LJS.EUndefined sp -> StampedFix sp $ Lit $ UndefinedL
  LJS.ENull sp -> StampedFix sp $ Lit $ NullL
  LJS.ELambda sp xs e -> StampedFix sp $ Func (map fromChars xs) (convert e)
  LJS.EObject sp fs -> StampedFix sp $ ObjE $ map (\ (x, e) -> (fromChars x, convert e)) fs
  LJS.EId sp x -> StampedFix sp $ Var $ fromChars x
  LJS.EOp sp o es -> StampedFix sp $ PrimOp o (map convert es)
  LJS.EApp sp e es -> StampedFix sp $ App (convert e) (map convert es)
  LJS.ELet sp xes e -> StampedFix sp $ Let (map (\ (x, e') -> (fromChars x, convert e')) xes) (convert e)
  LJS.ESetRef sp e₁ e₂ -> StampedFix sp $ RefSet (convert e₁) (convert e₂)
  LJS.ERef sp e -> StampedFix sp $ Ref (convert e)
  LJS.EDeref sp e -> StampedFix sp $ DeRef (convert e)
  LJS.EGetField sp e₁ e₂ -> StampedFix sp $ FieldRef (convert e₁) (convert e₂)
  LJS.EUpdateField sp e₁ e₂ e₃ -> StampedFix sp $ FieldSet (convert e₁) (convert e₂) (convert e₃)
  LJS.EDeleteField sp e₁ e₂ -> StampedFix sp $ Delete (convert e₁) (convert e₂)
  LJS.ESeq sp e₁ e₂ -> StampedFix sp $ Seq (convert e₁) (convert e₂)
  LJS.EIf sp e₁ e₂ e₃ -> StampedFix sp $ If (convert e₁) (convert e₂) (convert e₃)
  LJS.EWhile sp e₁ e₂ -> StampedFix sp $ While (convert e₁) (convert e₂)
  LJS.ELabel sp l e -> StampedFix sp $ LabelE (undefined l) (convert e)
  LJS.EBreak sp l e -> StampedFix sp $ Break (undefined l) (convert e)
  LJS.EThrow sp e -> StampedFix sp $ Throw (convert e)
  LJS.ECatch sp e₁ e₂ -> StampedFix sp $ TryCatch (convert e₁) undefined (convert e₂)
  LJS.EFinally sp e₁ e₂ -> StampedFix sp $ TryFinally (convert e₁) (convert e₂)
  LJS.ELet1 _sp _e _f -> error "HOAS should be translated away"
  LJS.ELet2 _sp _e₁ _e₂ _f -> error "HOAS should be translated away"
  LJS.EEval _sp -> error "HOAS should be translated away"

fromFile :: String -> IO Exp
fromFile fn = do
  js <- JS.parseFromFile $ toChars fn
  return $ convert $ LJS.removeHOAS $ LJS.desugar js id
