module Lang.JS.Glue where

import FP
import qualified FP.Pretty as P
import qualified Language.ECMAScript3 as JS
import qualified Language.LambdaJS.Syntax as LJS
import qualified Language.LambdaJS.Desugar as LJS
import qualified Language.LambdaJS.PrettyPrint as LJS
import qualified Language.LambdaJS.RemoveHOAS as LJS
import System.IO
import System.Directory
import Lang.JS.Syntax hiding (Exp)

type Exp = StampedFix JS.SourcePos (PreExp String)

convert :: LJS.ExprPos -> Exp
convert = \ case
  LJS.ENumber sp n -> StampedFix sp $ Lit $ D n
  LJS.EString sp s -> _
  LJS.EBool sp b -> _
  LJS.EUndefined sp -> _
  LJS.ENull sp -> _
  LJS.ELambda sp xs e -> _
  LJS.EObject sp fs -> _
  LJS.EId sp x -> _
  LJS.EOp sp o es -> _
  LJS.EApp sp e es -> _
  LJS.ELet sp xes e -> _
  LJS.ESetRef sp e₁ e₂ -> _
  LJS.ERef sp e -> _
  LJS.EDeref sp e -> _
  LJS.EGetField sp e₁ e₂ -> _
  LJS.EUpdateField sp e₁ e₂ e₃ -> _
  LJS.EDeleteField sp e₁ e₂ -> _
  LJS.ESeq sp e₁ e₂ -> _
  LJS.EIf sp e₁ e₂ e₃ -> _
  LJS.EWhile sp e₁ e₂ -> _
  LJS.ELabel sp l e -> _
  LJS.EBreak sp l e -> _
  LJS.EThrow sp e -> _
  LJS.ECatch sp e₁ e₂ -> _
  LJS.EFinally sp e₁ e₂ -> _
  -- |We use HOAS when possible so that we don't mess up bindings.  When
  -- pretty-printing, we unravel these to use conventional bindings.
  LJS.ELet1 sp e f -> error "HOAS should be translated away"
  LJS.ELet2 sp e₁ e₂ f -> error "HOAS should be translated away"
  LJS.EEval sp -> error "HOAS should be translated away"

main :: IO ()
main = do
  jsFiles <- map (("benchmarks/" ++ ) . fromChars) . filter notHidden ^$ getDirectoryContents (toChars "benchmarks")
  traverseOn jsFiles $ \ jsFile -> do
    js <- JS.parseFromFile $ toChars jsFile
    let lamjs = LJS.removeHOAS $ LJS.desugar js id
    pprint $ (P.text $ fromChars $ LJS.pretty lamjs :: Doc)
  where
    notHidden ('.':_) = False
    notHidden _ = True


