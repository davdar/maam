module Lang.LamIf.Pretty where

import FP
import Lang.LamIf.Val
import qualified FP.Pretty as P
import Lang.LamIf.StateSpace
import Lang.LamIf.CPS as C
import Lang.LamIf.Syntax as L

instance Pretty RawName where
  pretty (RawName s) = P.bdr s
instance Pretty LocNum where
  pretty (LocNum i) = P.pun $ ptoString i
instance Pretty BdrNum where
  pretty (BdrNum i) = P.format (P.setFG $ fmn 2) $ P.text $ ptoString i
instance Pretty GenName where
  pretty (GenName iM s) = exec
    [ pretty s
    , maybeElimOn iM (return ()) $ \ i -> exec [P.pun "#", P.pun $ show i]
    ]

instance Pretty Lit where
  pretty (I i) = pretty i
  pretty (B b) = pretty b

instance Pretty BinOp where
  pretty Add = P.keyPun "+"
  pretty Sub = P.keyPun "-"
  pretty GTE = P.keyPun ">="

data VarLam n e = VarLam [n] e
instance (Pretty n, Pretty e) => Pretty (VarLam n e) where
  pretty (VarLam xs e) = P.atLevel (toi 0) $ P.nest (toi 2) $ P.hvsep
    [ P.hsep $ concat
      [ single $ P.key "λ"
      , map pretty xs
      , single $ P.keyPun "->"
      ]
    , pretty e
    ]

instance (Pretty n, Pretty e) => Pretty (PreExp n e) where
  pretty (L.Lit l) = pretty l
  pretty (L.Var n) = pretty n
  pretty (L.Lam n e) = P.atLevel (toi 0) $ pretty $ VarLam [n] e
  pretty (L.Prim o e1 e2) = P.infr (lbinOpLevel o) (pretty $ lbinOpOp o) (pretty e1) (pretty e2)
  pretty (L.Let n e b) = P.atLevel (toi 0) $ P.hvsep
    [ P.botLevel $ P.hsep [P.key "let", pretty n, P.keyPun ":=", P.hvsep [P.nest (toi 2) $ pretty e, P.key "in"]]
    , P.hsep [pretty b]
    ]
  pretty (L.App fe e) = P.app (pretty fe) [pretty e]
  pretty (L.If e te fe) = P.atLevel (toi 0) $ P.nest (toi 2) $ P.hvsep
    [ P.botLevel $ P.hsep [P.key "if", P.align $ pretty e]
    , P.botLevel $ P.hvsep [P.key "then", P.align $ pretty te]
    , P.hvsep [P.key "else", P.align $ pretty fe]
    ]
  pretty (L.Tup e1 e2) = P.collection "<" ">" "," [pretty e1, pretty e2]
  pretty (L.Pi1 e) = P.pre (toi 100) (P.key "fst") (pretty e)
  pretty (L.Pi2 e) = P.pre (toi 100) (P.key "snd") (pretty e)
instance (Pretty n) => Functorial Pretty (PreExp n) where
  functorial = W

instance (Pretty n) => Pretty (PrePico n) where
  pretty (C.Lit l) = pretty l
  pretty (C.Var x) = pretty x

instance (Pretty n, Pretty c) => Pretty (PreAtom n c) where
  pretty (C.Pico p) = pretty p
  pretty (C.Prim o a1 a2) = P.infr (lbinOpLevel o) (pretty $ lbinOpOp o) (pretty a1) (pretty a2)
  pretty (C.LamF x kx c) = pretty $ VarLam [x, kx] c
  pretty (C.LamK x c) = pretty $ VarLam [x] c
  pretty (C.Tup a1 a2) = P.collection "<" ">" "," [pretty a1, pretty a2]
  pretty (C.Pi1 a) = P.hsep [P.key "fst", pretty a]
  pretty (C.Pi2 a) = P.hsep [P.key "snd", pretty a]

instance (Pretty n, Pretty c) => Pretty (PreCall n c) where
  pretty (C.Let x aa c) = P.atLevel (toi 0) $ P.mustBreak $ P.vsep
    [ P.hsep [pretty x, P.keyPun ":=", pretty aa]
    , pretty c
    ]
  pretty (C.If x tc fc) = P.atLevel (toi 0) $ P.nest (toi 2) $ P.hvsep $ map (P.nest (toi 2))
    [ P.hsep [P.key "if", P.botLevel $ pretty x]
    , P.hvsep [P.key "then", P.botLevel $ pretty tc]
    , P.hvsep [P.key "else", pretty fc]
    ]
  pretty (AppF fx ax kx) = P.app (pretty fx) [pretty ax, pretty kx]
  pretty (AppK kx ax) = P.app (pretty kx) [pretty ax]
  pretty (Halt ax) = P.app (P.key "HALT") [pretty ax]
instance (Pretty n) => Functorial Pretty (PreCall n) where
  functorial = W

instance (Pretty lτ, Pretty dτ) => Pretty (Addr lτ dτ) where
  pretty (Addr loc lτ dτ) = P.collection "<" ">" "," 
    [ exec [P.pun "x=", P.align $ pretty loc]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    , exec [P.pun "dτ=", P.align $ pretty dτ]
    ]

instance (Pretty lτ, Pretty dτ) => Pretty (Clo lτ dτ) where
  pretty (Clo l _xs _c _ρ lτ) = P.collection "<" ">" "," 
    [ exec [P.pun "λ=", pretty l]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    ]

makePrettyUnion ''𝒮Cxt
makePrettyUnion ''𝒮
makePrettyUnion ''PicoVal

instance (Pretty lτ, Pretty dτ) => Pretty (CVal lτ dτ) where
  pretty (LitC l) = pretty l
  pretty (CloC c) = pretty c
  pretty BotC = P.lit "⊥"
  pretty (TupC (pv1, pv2)) = P.collection "<" ">" "," [pretty pv1, pretty pv2]

instance (Pretty lτ, Pretty dτ) => Pretty (AVal lτ dτ) where
  pretty (LitA l) = pretty l
  pretty IA = P.lit "INT"
  pretty BA = P.lit "BOOL"
  pretty (CloA c) = pretty c
  pretty BotA = P.lit "⊥"
  pretty (TupA (pv1, pv2)) = P.collection "<" ">" "," [pretty pv1, pretty pv2]

deriving instance (Pretty (val lτ dτ)) => Pretty (Power val lτ dτ)
