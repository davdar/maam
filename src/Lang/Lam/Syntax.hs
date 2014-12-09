module Lang.Lam.Syntax where

import FP
import qualified FP.Pretty as P
import Lang.Common

data PreExp n e = 
    Lit Lit
  | Var n
  | Lam n e
  | Prim Op e
  | Let n e e
  | App e e
  | If e e e
  deriving (Eq, Ord)
type Exp = Fix (PreExp Name)
type SExp = StampedFix LocNum (PreExp SName)

instance (Pretty n, Pretty e) => Pretty (PreExp n e) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Lam n e) = pretty $ VarLam [n] e
  pretty (Prim o e) = P.app [pretty o, pretty e]
  pretty (Let n e b) = P.atLevel 0 $ P.hvsep
    [ P.hsep [P.key "let", pretty n, P.keyPun ":=", P.hvsep [P.nest 2 $ P.botLevel $ pretty e, P.key "in"]]
    , P.hsep [pretty b]
    ]
  pretty (App fe e) = P.app [pretty fe, pretty e]
  pretty (If e te fe) = P.atLevel 0 $ P.nest 2 $ P.hvsep $ map (P.nest 2)
    [ P.hsep [P.key "if", P.botLevel $ pretty e]
    , P.hvsep [P.key "then", P.botLevel $ pretty te]
    , P.hvsep [P.key "else", pretty fe]
    ]
instance (Pretty n) => Functorial Pretty (PreExp n) where
  functorial = W
