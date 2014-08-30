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

instance (Pretty n) => Pretty (PrePico n) where
  pretty (Lit l) = pretty l
  pretty (Var x) = pretty x
instance (Pretty n, Pretty c) => Pretty (PreAtom n c) where
  pretty (Pico p) = pretty p
  pretty (Prim o a) = P.app [pretty o, pretty a]
  pretty (LamF x kx c) = prettyLam [x, kx] c
  pretty (LamK x c) = prettyLam [x] c

instance (Pretty n, Pretty c) => Pretty (PreCall n c) where
  pretty (Let x aa c) = P.parensIfWrapped $ P.mustBreak $ P.vsep
    [ P.hsep [pretty x, P.pun ":=", pretty aa]
    , pretty c
    ]
  pretty (If x tc fc) = P.parensIfWrapped $ P.nest 2 $ P.hvsep $ map (P.nest 2)
    [ P.hsep [P.key "if", pretty x]
    , P.hvsep [P.key "then", pretty tc]
    , P.hvsep [P.key "else", pretty fc]
    ]
  pretty (AppF fx ax kx) = P.app [pretty fx, pretty ax, pretty kx]
  pretty (AppK kx ax) = P.app [pretty kx, pretty ax]
  pretty (Halt ax) = P.app [P.key "HALT", pretty ax]
instance (Pretty n) => Functorial Pretty (PreCall n) where
  functorial = W
