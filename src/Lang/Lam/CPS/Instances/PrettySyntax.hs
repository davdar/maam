module Lang.Lam.CPS.Instances.PrettySyntax where

import Lang.Lam.CPS.Syntax
import FP
import qualified FP.Pretty as P
import Lang.Lam.Instances.PrettySyntax ()

prettyLam :: (Pretty n, Pretty c) => [n] -> c -> Doc
prettyLam xs c = P.parensIfWrapped $ P.nest 2 $ P.hvsep
  [ exec [P.hsep $ P.key "λ" : map pretty xs, P.pun "."]
  , pretty c
  ]

instance (Pretty n, Pretty c) => Pretty (PreAtom n c) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Prim o a) = P.app [pretty o, pretty a]
  pretty (LamF x kx c) = prettyLam [x, kx] c
  pretty (LamK x c) = prettyLam [x] c

instance (Pretty n, Pretty c) => Pretty (PreCall n c) where
  pretty (If a tc fc) = P.parensIfWrapped $ P.nest 2 $ P.hvsep $ map (P.nest 2)
    [ P.hsep [P.key "if", pretty a]
    , P.hvsep [P.key "then", pretty tc]
    , P.hvsep [P.key "else", pretty fc]
    ]
  pretty (AppK (LamK x c) ae) = P.mustBreak $ P.vsep
    [ P.hsep [pretty x, P.keyPun ":=", pretty ae]
    , pretty c
    ]
  pretty (AppF f ae (LamK k c)) = P.mustBreak $ P.vsep
    [ P.nest 2 $ P.hvsep
        [ P.hsep [pretty k, P.pun "<-"]
        , P.app [pretty f, pretty ae]
        ]
    , pretty c
    ]
  pretty (AppF fa ea ka) = P.app [pretty fa, pretty ea, pretty ka]
  pretty (AppK ka ea) = P.app [pretty ka, pretty ea]
  pretty (Halt ae) = P.app [P.key "HALT", pretty ae]
instance (Pretty n) => Functorial Pretty (PreCall n) where
  functorial = W
