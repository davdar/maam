module Lang.CPS.Pretty where

import FP
import Lang.CPS.Val
import qualified FP.Pretty as P
import Lang.CPS.StateSpace
import Lang.CPS.Syntax
import Lang.Common

instance (Pretty n) => Pretty (PrePico n) where
  pretty (Lit l) = pretty l
  pretty (Var x) = pretty x
instance (Pretty n, Pretty c) => Pretty (PreAtom n c) where
  pretty (Pico p) = pretty p
  pretty (Prim o a) = P.app (pretty o) [pretty a]
  pretty (LamF x kx c) = pretty $ VarLam [x, kx] c
  pretty (LamK x c) = pretty $ VarLam [x] c

instance (Pretty n, Pretty c) => Pretty (PreCall n c) where
  pretty (Let x aa c) = P.atLevel 0 $ P.mustBreak $ P.vsep
    [ P.hsep [pretty x, P.pun ":=", pretty aa]
    , pretty c
    ]
  pretty (If x tc fc) = P.atLevel 0 $ P.nest 2 $ P.hvsep $ map (P.nest 2)
    [ P.hsep [P.key "if", P.botLevel $ pretty x]
    , P.hvsep [P.key "then", P.botLevel $ pretty tc]
    , P.hvsep [P.key "else", pretty fc]
    ]
  pretty (AppF fx ax kx) = P.app (pretty fx) [pretty ax, pretty kx]
  pretty (AppK kx ax) = P.app (pretty kx) [pretty ax]
  pretty (Halt ax) = P.app (P.key "HALT") [pretty ax]
instance (Pretty n) => Functorial Pretty (PreCall n) where
  functorial = W

instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (Addr lτ dτ ψ) where
  pretty (Addr loc lτ dτ) = P.collection "<" ">" "," 
    [ exec [P.pun "x=", P.align $ pretty loc]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    , exec [P.pun "dτ=", P.align $ pretty dτ]
    ]

instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (Clo lτ dτ ψ) where
  pretty (Clo l _xs _c _ρ lτ) = P.collection "<" ">" "," 
    [ exec [P.pun "λ=", pretty l]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    ]

makePrettyUnion ''𝒮

instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (CVal lτ dτ ψ) where
  pretty (LitC l) = pretty l
  pretty (CloC c) = pretty c
  pretty BotC = P.lit "⊥"

instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (AVal lτ dτ ψ) where
  pretty (LitA l) = pretty l
  pretty IA = P.lit "INT"
  pretty BA = P.lit "BOOL"
  pretty (CloA c) = pretty c
  pretty BotA = P.lit "⊥"

deriving instance (Pretty (val lτ dτ ψ)) => Pretty (Power val lτ dτ ψ)
