module Lang.Hask.Pretty where

import Outputable
import Lang.Hask.Compat
import FP
import qualified FP.Pretty as P
import Lang.Hask.CPS
import Lang.Hask.Semantics
import DataCon
import Name
import Literal
import CoreSyn (AltCon(..))

makePrettyUnion ''Pico
makePrettySum ''Moment
makePrettySum ''Addr
makePrettySum ''ArgVal
makePrettySum ''Data
makePrettySum ''FunClo
makePrettySum ''Ref
makePrettySum ''KonClo
makePrettySum ''ThunkClo
makePrettySum ''KonMemoClo
makePrettySum ''Forced
makePrettySum ''𝒮

instance Pretty Name where pretty = P.bdr . fromChars . showSDoc (dynFlags ()) . ppr
instance Pretty Literal where pretty = P.lit . fromChars . showSDoc (dynFlags ()) . ppr
instance Pretty DataCon where pretty = P.con . fromChars . showSDoc (dynFlags ()) . ppr

instance Pretty AltCon where 
  pretty (DataAlt dc) = pretty dc
  pretty (LitAlt l) = pretty l
  pretty DEFAULT = P.key "DEFAULT"

data VarLam n e = VarLam [n] e
instance (Pretty n, Pretty e) => Pretty (VarLam n e) where
  pretty (VarLam xs e) = P.nest 2 $ P.hvsep
    [ P.hsep $ concat
      [ single $ P.key "λ"
      , map pretty xs
      , single $ P.keyPun "->"
      ]
    , pretty e
    ]

instance (Pretty e) => Pretty (PreAtom e) where
  pretty (Pico p) = pretty p
  pretty (LamF x k e) = pretty $ VarLam [x, k] e
  pretty (LamK x e) = pretty $ VarLam [x] e
  pretty (Thunk r xi x k p₁ p₂) = exec
    [ P.key "THUNK"
    , P.collection "[" "]" "," [ pretty r , P.pun $ show xi , pretty x , pretty k ]
    , P.parens $ P.app (pretty p₁) [pretty p₂]
    ]

instance (Pretty e) => Pretty (PreCaseBranch e) where
  pretty (CaseBranch con cs e) = P.nest 2 $ P.hvsep
    [ P.hsep
        [ P.app (pretty con) $ map pretty cs
        , P.keyPun "->"
        ]
    , P.nest 2 $ pretty e
    ]

instance (Pretty e) => Pretty (PreCall e) where
  pretty (Let x a e) = P.hvsep
    [ P.hsep [P.key "let", pretty x, P.keyPun ":=", P.hvsep [P.nest 2 $ pretty a, P.key "in"]]
    , pretty e
    ]
  pretty (Rec rxs e) = P.hvsep
    [ P.hsep $ concat [single $ P.key "rec", map pretty rxs, single $ P.key "in"]
    , pretty e
    ]
  pretty (Letrec xas e) = P.hvsep
    [ P.key "letrec"
    , exec 
        [ P.space 2
        , P.align $ P.hvsep $ mapOn xas $ \ (x, a) -> P.hsep [pretty x, P.keyPun ":=" , P.nest 2 $ pretty a]
        ]
    , P.key "in"
    , pretty e
    ]
  pretty (AppK p₁ p₂) = P.parens $ P.app (P.con "K") [pretty p₁, pretty p₂]
  pretty (AppF xi x p₁ p₂ p₃) = 
    P.app (exec [P.con "F", P.collection "[" "]" "," [P.pun $ show xi, pretty x]]) 
          [pretty p₁, pretty p₂, pretty p₃]
  pretty (Case xi x p bs) = P.hvsep
    [ exec
        [ P.key "CASE["
        , P.pun $ show xi
        , P.pun ","
        , pretty x
        , P.key "]"
        , P.parens $ pretty p
        ]
    , P.key "of"
    , exec
        [ P.space 2
        , P.align $ P.hvsep $ map pretty bs 
        ]
    ]
  pretty (Halt p) = P.app (P.con "HALT") [pretty p]
instance (Functorial Pretty PreCall) where functorial = W
