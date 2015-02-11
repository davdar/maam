module Lang.Lam.Syntax where

import FP
import qualified FP.Pretty as P
import Lang.Common

data PreExp n e = 
    Lit Lit
  | Var n
  | Lam n e
  | Prim LBinOp e e
  | Let n e e
  | App e e
  | If e e e
  deriving (Eq, Ord)
type Exp = Fix (PreExp Name)
type SExp = StampedFix LocNum (PreExp SName)

instance (Pretty n, Pretty e) => Pretty (PreExp n e) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Lam n e) = P.atLevel 0 $ pretty $ VarLam [n] e
  pretty (Prim o e1 e2) = P.infr (lbinOpLevel o) (pretty $ lbinOpOp o) (pretty e1) (pretty e2)
  pretty (Let n e b) = P.atLevel 0 $ P.hvsep
    [ P.botLevel $ P.hsep [P.key "let", pretty n, P.keyPun ":=", P.hvsep [P.nest 2 $ pretty e, P.key "in"]]
    , P.hsep [pretty b]
    ]
  pretty (App fe e) = P.app (pretty fe) [pretty e]
  pretty (If e te fe) = P.atLevel 0 $ P.nest 2 $ P.hvsep
    [ P.botLevel $ P.hsep [P.key "if", P.align $ pretty e]
    , P.botLevel $ P.hvsep [P.key "then", P.align $ pretty te]
    , P.hvsep [P.key "else", P.align $ pretty fe]
    ]
instance (Pretty n) => Functorial Pretty (PreExp n) where
  functorial = W
