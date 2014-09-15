module Lang.Lam.CPS.Instances.Delta where

import FP
import MAAM
import Lang.Lam.CPS.Classes.Delta
import qualified FP.Pretty as P
import Lang.Lam.Syntax (Lit(..), coerceI, coerceB, Op(..))

-- Concrete {{{

data Cδ
cδ :: P Cδ
cδ = P

data CVal μ = LitC Lit | CloC (Clo μ)
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (CVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (CVal μ)
instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (CVal μ) where
  pretty (LitC l) = pretty l
  pretty (CloC c) = pretty c

coerceLitC :: CVal μ -> Maybe Lit
coerceLitC (LitC l) = Just l
coerceLitC _ = Nothing
coerceCloC :: CVal μ -> Maybe (Clo μ)
coerceCloC (CloC c) = Just c
coerceCloC _ = Nothing

newtype SetCVal μ = SetCVal { runSetCVal :: Set (CVal μ) }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (SetCVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (SetCVal μ)
deriving instance HasBot (SetCVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => JoinLattice (SetCVal μ)
deriving instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (SetCVal μ)
setCValL :: Lens (SetCVal μ) (Set (CVal μ))
setCValL = isoLens runSetCVal SetCVal

instance Delta Cδ where
  type Val Cδ = SetCVal
  type Δ Cδ μ = (Ord (Addr μ), Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ))
  lit :: (Δ Cδ μ) => P Cδ -> Lit -> Val Cδ μ
  lit P = SetCVal . ssingleton . LitC
  clo :: (Δ Cδ μ) => P Cδ -> Clo μ -> Val Cδ μ
  clo P = SetCVal . ssingleton . CloC
  op :: (Δ Cδ μ) => P Cδ -> Op -> Val Cδ μ -> Val Cδ μ
  op P Add1     = update setCValL $ cmap (LitC . I) . extend (cmap (+1)    . cuseMaybeZero . coerceI *. coerceLitC)
  op P Sub1     = update setCValL $ cmap (LitC . I) . extend (cmap (+(-1)) . cuseMaybeZero . coerceI *. coerceLitC)
  op P IsNonNeg = update setCValL $ cmap (LitC . B) . extend (cmap (>=0)   . cuseMaybeZero . coerceI *. coerceLitC)
  elimBool :: (Δ Cδ μ) => P Cδ -> Val Cδ μ -> Set Bool
  elimBool P = extend (useMaybeSet . coerceB *. coerceLitC) . runSetCVal
  elimClo :: (Δ Cδ μ) => P Cδ -> Val Cδ μ -> Set (Clo μ)
  elimClo P = extend (useMaybeSet . coerceCloC) . runSetCVal

-- }}}

-- Abstract {{{

data Aδ
aδ :: P Aδ
aδ = P

data AVal μ = LitA Lit | IA | CloA (Clo μ)
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (AVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (AVal μ)
instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (AVal μ) where
  pretty (LitA l) = pretty l
  pretty IA = P.lit "INT"
  pretty (CloA c) = pretty c

coerceIA :: AVal μ -> Maybe ()
coerceIA IA = Just ()
coerceIA _ = Nothing
coerceLitA :: AVal μ -> Maybe Lit
coerceLitA (LitA l) = Just l
coerceLitA _ = Nothing
coerceIOrIntA :: AVal μ -> Maybe ()
coerceIOrIntA = mftries [ coerceIA , void . coerceI *. coerceLitA ]
coerceBoolA :: AVal μ -> Set Bool
coerceBoolA v = cuseMaybeZero $ coerceB *$ coerceLitA v
coerceCloA :: AVal μ -> Maybe (Clo μ)
coerceCloA (CloA c) = Just c
coerceCloA _ = Nothing

newtype SetAVal μ = SetAVal { runSetAVal :: Set (AVal μ) }
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (SetAVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (SetAVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => PartialOrder (SetAVal μ)
deriving instance HasBot (SetAVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => JoinLattice (SetAVal μ)
deriving instance (Pretty (LexicalTime μ Ψ), Pretty (DynamicTime μ Ψ)) => Pretty (SetAVal μ)
runSetAValL :: Lens (SetAVal μ) (Set (AVal μ))
runSetAValL = isoLens runSetAVal SetAVal

instance Delta Aδ where
  type Val Aδ = SetAVal
  type Δ Aδ μ = (Ord (Addr μ), Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ))
  lit :: (Δ Aδ μ) => P Aδ -> Lit -> Val Aδ μ
  lit P (I i) = SetAVal $ ssingleton $ LitA $ I i
  lit P (B b) = SetAVal $ ssingleton $ LitA $ B b
  clo :: (Δ Aδ μ) => P Aδ -> Clo μ -> Val Aδ μ
  clo P = SetAVal . ssingleton . CloA
  op :: forall μ. (Δ Aδ μ) => P Aδ -> Op -> Val Aδ μ -> Val Aδ μ
  op P Add1     = update runSetAValL $ cmap (const IA) . extend (cuseMaybeZero . coerceIOrIntA)
  op P Sub1     = update runSetAValL $ cmap (const IA) . extend (cuseMaybeZero . coerceIOrIntA)
  op P IsNonNeg = update runSetAValL $ extend $ mfsum
    [ cmap (LitA . B . (>=0)) . cuseMaybeZero . coerceI *. coerceLitA
    , cmap (LitA . B) . extend (const $ fromList [True, False]) . cuseMaybeZero . coerceIA
    ]
  elimBool :: (Δ Aδ μ) => P Aδ -> Val Aδ μ -> Set Bool
  elimBool P = extend coerceBoolA . runSetAVal
  elimClo :: (Δ Aδ μ) => P Aδ -> Val Aδ μ -> Set (Clo μ)
  elimClo P = extend (useMaybeSet . coerceCloA) . runSetAVal

-- }}}
