module Lang.CPS.Syntax where

import FP
import qualified FP.Pretty as P
import MAAM

data Lit = I Integer | B Bool
  deriving (Eq, Ord)
coerceI :: Lit -> Maybe Integer
coerceI (I i) = Just i
coerceI _ = Nothing
coerceB :: Lit -> Maybe Bool
coerceB (B b) = Just b
coerceB _ = Nothing
instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b

instance PartialOrder Lit where pcompare = discreteOrder
data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance Pretty Op where
  pretty Add1 = P.key "+1"
  pretty Sub1 = P.key "-1"
  pretty IsNonNeg = P.key ">=0?"
instance PartialOrder Op where pcompare = discreteOrder
data Atom =
    LitA Lit
  | Var Name
  | Prim Op Atom
  | Lam [Name] Call
  deriving (Eq, Ord)
instance Pretty Atom where
  pretty (LitA l) = pretty l
  pretty (Var n) = P.text n
  pretty (Prim o a) = P.app (prettyParen o) [prettyParen a]
  pretty (Lam xs c) = P.app (lambda >> P.space 1 >> binders >> dot) [pretty c]
    where
      lambda = P.key"λ"
      binders = exec $ intersperse (P.space 1) $ map P.bdr xs
      dot = P.pun "."
  prettyParen (Prim o a) = P.parens $ pretty $ Prim o a
  prettyParen (Lam xs c) = P.parens $ pretty $ Lam xs c
  prettyParen a = pretty a
instance PartialOrder Atom where pcompare = discreteOrder
data Call =
    If Atom Call Call
  | App Atom [Atom]
  | Halt Atom
  deriving (Eq, Ord)
instance Pretty Call where
  pretty (If a tc fc) = P.app (ifKwd >> P.space 1 >> P.align (pretty a)) [trueBranch, falseBranch]
    where
      ifKwd = P.key "if"
      trueBranch = P.app (P.key "then") [pretty tc]
      falseBranch = P.app (P.key "else") [pretty fc]
  pretty (App (Lam [x] c) [ae]) = do
    P.whenFlat mzero
    name >> P.space 1 >> gets >> P.space 1 >> pretty ae
    P.newline
    pretty c
    where
      name = P.bdr x
      gets = P.pun ":="
  pretty (App f [ae, Lam [k] c]) = do
    P.whenFlat mzero
    P.app (name >> P.space 1 >> gets >> P.space 1 >> prettyParen f) [prettyParen ae]
    P.newline
    pretty c
    where
      name = P.bdr k
      gets = P.pun "<-"
  pretty (App ae aes) = P.app (prettyParen ae) (map prettyParen aes)
  pretty (Halt ae) = P.app halt [prettyParen ae]
    where
      halt = P.key "halt"
  prettyParen = P.parens . pretty
instance PartialOrder Call where pcompare = discreteOrder
