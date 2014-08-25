module Lang.CPS.Syntax.Pretty where

import Lang.CPS.Syntax.AST
import FP
import qualified FP.Pretty as P

instance Pretty SName where
  pretty (SName iM s) = P.format P.bdrFmt $ do
    P.text s 
    case iM of
      Nothing -> return ()
      Just i -> do
        P.text "["
        P.text $ toString i
        P.text "]"
instance Pretty RName where
  pretty (RName i n) = pretty n >> P.bdr "@" >> P.bdr (toString i)
instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b

instance Pretty Op where
  pretty Add1 = P.key "+1"
  pretty Sub1 = P.key "-1"
  pretty IsNonNeg = P.key ">=0?"

instance (Pretty n, Pretty c) => Pretty (Atom n c) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Prim o a) = P.app (prettyParen o) [prettyParen a]
  pretty (Lam xs c) = P.app (lambda >> P.space 1 >> binders >> dot) [pretty c]
    where
      lambda = P.key"λ"
      binders = exec $ intersperse (P.space 1) $ map (P.format P.bdrFmt . pretty) xs
      dot = P.pun "."
  prettyParen (Prim o a) = P.parens $ pretty $ Prim o a
  prettyParen (Lam xs c) = P.parens $ pretty $ Lam xs c
  prettyParen a = pretty a

instance (Pretty n, Pretty c) => Pretty (Call n c) where
  pretty (If a tc fc) = P.app (ifKwd >> P.space 1 >> P.align (pretty a)) [trueBranch, falseBranch]
    where
      ifKwd = P.key "if"
      trueBranch = P.app (P.key "then") [pretty tc]
      falseBranch = P.app (P.key "else") [pretty fc]
  pretty (App (Lam [x] c) [ae]) = do
    P.whenFlat mzero
    prettyName >> P.space 1 >> gets >> P.space 1 >> pretty ae
    P.newline
    pretty c
    where
      prettyName = P.format P.bdrFmt $ pretty x
      gets = P.pun ":="
  pretty (App f [ae, Lam [k] c]) = do
    P.whenFlat mzero
    P.app (prettyName >> P.space 1 >> gets >> P.space 1 >> prettyParen f) [prettyParen ae]
    P.newline
    pretty c
    where
      prettyName = P.format P.bdrFmt $ pretty k
      gets = P.pun "<-"
  pretty (App ae aes) = P.app (prettyParen ae) (map prettyParen aes)
  pretty (Halt ae) = P.app prettyHalt [prettyParen ae]
    where
      prettyHalt = P.key "halt"
  prettyParen = P.parens . pretty
instance Pretty SCall where
  pretty = pretty . runFix
instance Pretty RCall where
  pretty (RCall i c) = P.pun (toString i) >> P.text ":" >> pretty c
