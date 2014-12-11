module Lang.JS.Glue where

import FP
import qualified FP.Pretty as P
import qualified Language.ECMAScript3 as JS
import qualified Language.LambdaJS.Syntax as LJS
import qualified Language.LambdaJS.Desugar as LJS
import qualified Language.LambdaJS.PrettyPrint as LJS
import qualified Language.LambdaJS.RemoveHOAS as LJS
import System.Directory
import Lang.JS.Syntax hiding (Exp)

type Exp = StampedFix JS.SourcePos (PreExp String Label)

instance Pretty SourcePos where

convert :: LJS.ExprPos -> Exp
convert = \ case
  LJS.ENumber sp n -> StampedFix sp $ Lit $ D n
  LJS.EString sp s -> StampedFix sp $ Lit $ S $ fromChars s
  LJS.EBool sp b -> StampedFix sp $ Lit $ B b
  LJS.EUndefined sp -> StampedFix sp $ Lit $ UndefinedL
  LJS.ENull sp -> StampedFix sp $ Lit $ NullL
  LJS.ELambda sp xs e -> StampedFix sp $ undefined
  LJS.EObject sp fs -> StampedFix sp $ ObjE $ map (\ (x, e) -> (fromChars x, convert e)) fs
  LJS.EId sp x -> StampedFix sp $ Var $ fromChars x
  LJS.EOp sp o es -> StampedFix sp $ undefined
  LJS.EApp sp e es -> StampedFix sp $ undefined
  LJS.ELet sp xes e -> StampedFix sp $ undefined
  LJS.ESetRef sp e₁ e₂ -> StampedFix sp $ undefined
  LJS.ERef sp e -> StampedFix sp $ undefined
  LJS.EDeref sp e -> StampedFix sp $ undefined
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
  LJS.ELet1 sp e f -> error "HOAS should be translated away"
  LJS.ELet2 sp e₁ e₂ f -> error "HOAS should be translated away"
  LJS.EEval sp -> error "HOAS should be translated away"

fromFile :: String -> IO Exp
fromFile fn = do
  js <- JS.parseFromFile $ toChars fn
  return $ convert $ LJS.removeHOAS $ LJS.desugar js id

main :: IO ()
main = do
  jsFiles <- map (("benchmarks/" ++) . fromChars) . filter (not . hidden) ^$ getDirectoryContents $ toChars "benchmarks"
  traverseOn jsFiles $ \ jsFile -> do
    e <- fromFile jsFile
    pprint e
  where
    hidden ('.':_) = True
    hidden _ = True
