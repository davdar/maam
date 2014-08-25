module Lang.Lam.CPS.Instances.PrettySyntax where

import Lang.Lam.CPS.Syntax
import FP
import qualified FP.Pretty as P
import Lang.Lam.Instances.PrettySyntax ()

prettyLam :: (Pretty n, Pretty c) => [n] -> c -> Doc
prettyLam xs c = P.app (P.key "λ" >> P.space 1 >> binders >> P.pun ".") [pretty c]
  where
    binders = exec $ intersperse (P.space 1) $ map (P.format P.bdrFmt . pretty) $ xs

instance (Pretty n, Pretty c) => Pretty (PreAtom n c) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Prim o a) = P.app (prettyParen o) [prettyParen a]
  pretty (LamF x kx c) = prettyLam [x, kx] c
  pretty (LamK x c) = prettyLam [x] c
  prettyParen (Prim o a) = P.parens $ pretty $ Prim o a
  prettyParen (LamF x kx c) = P.parens $ pretty $ LamF x kx c
  prettyParen (LamK x c) = P.parens $ pretty $ LamK x c
  prettyParen a = pretty a

instance (Pretty n, Pretty c) => Pretty (PreCall n c) where
  pretty (If a tc fc) = P.app (ifKwd >> P.space 1 >> P.align (pretty a)) [trueBranch, falseBranch]
    where
      ifKwd = P.key "if"
      trueBranch = P.app (P.key "then") [pretty tc]
      falseBranch = P.app (P.key "else") [pretty fc]
  pretty (AppK (LamK x c) ae) = do
    P.whenFlat mzero
    prettyName >> P.space 1 >> gets >> P.space 1 >> pretty ae
    P.newline
    pretty c
    where
      prettyName = P.format P.bdrFmt $ pretty x
      gets = P.pun ":="
  pretty (AppF f ae (LamK k c)) = do
    P.whenFlat mzero
    P.app (prettyName >> P.space 1 >> gets >> P.space 1 >> prettyParen f) [prettyParen ae]
    P.newline
    pretty c
    where
      prettyName = P.format P.bdrFmt $ pretty k
      gets = P.pun "<-"
  pretty (AppF fa ea ka) = P.app (prettyParen fa) $ map prettyParen [ea, ka]
  pretty (AppK ka ea) = P.app (prettyParen ka) $ [prettyParen ea]
  pretty (Halt ae) = P.app prettyHalt [prettyParen ae]
    where
      prettyHalt = P.key "halt"
  prettyParen = P.parens . pretty
instance (Pretty n) => Functorial Pretty (PreCall n) where
  functorial = W
