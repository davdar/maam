module Lang.Lam.Instances.PrettySyntax where

import FP
import Lang.Lam.Syntax
import qualified FP.Pretty as P

instance Pretty Name where
  pretty (Name s) = P.bdr s
instance Pretty LocNum where
  pretty (LocNum i) = P.pun $ ptoString i
instance Pretty BdrNum where
  pretty (BdrNum i) = P.format (P.setFG 2) $ P.text $ ptoString i
instance Pretty GName where
  pretty (GName iM s) = exec
    [ pretty s
    , maybeOn iM (return ()) $ \ i -> exec [P.pun "#", P.pun $ toString i]
    ]
instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b
instance Pretty Op where
  pretty Add1 = P.key "+1"
  pretty Sub1 = P.key "-1"
  pretty IsNonNeg = P.key ">=0?"

instance (Pretty n, Pretty e) => Pretty (PreExp n e) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Lam n e) = P.parensIfWrapped $ P.nest 2 $ P.hvsep 
    [ exec [P.hsep [P.key "λ", P.pretty n], P.pun "."]
    , pretty e
    ]
  pretty (Prim o e) = P.app [pretty o, pretty e]
  pretty (Let n e b) = P.parensIfWrapped $ P.hvsep
    [ P.hsep [P.key "let", pretty n, P.keyPun ":=", P.hvsep [P.nest 2 $ pretty e, P.key "in"]]
    , P.hsep [pretty b]
    ]
  pretty (App fe e) = P.app [pretty fe, pretty e]
  pretty (If e te fe) = P.parensIfWrapped $ P.nest 2 $ P.hvsep $ map (P.nest 2)
    [ P.hsep [P.key "if", pretty e]
    , P.hvsep [P.key "then", pretty te]
    , P.hvsep [P.key "else", pretty fe]
    ]
instance (Pretty n) => Functorial Pretty (PreExp n) where
  functorial = W
