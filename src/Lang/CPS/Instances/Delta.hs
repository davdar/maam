module Lang.CPS.Instances.Delta where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

--------------
-- Concrete --
--------------

data Cδ
cδ :: P Cδ
cδ = P

data CVal μ = LitC Lit | CloC (Clo μ)
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (CVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (CVal μ)

coerceLitC :: CVal μ -> Maybe Lit
coerceLitC (LitC l) = Just l
coerceLitC _ = Nothing
coerceCloC :: CVal μ -> Maybe (Clo μ)
coerceCloC (CloC c) = Just c
coerceCloC _ = Nothing

newtype SetCVal μ = SetCVal { runSetCVal :: Set (CVal μ) }
runSetCValL :: Lens (SetCVal μ) (Set (CVal μ))
runSetCValL = isoLens runSetCVal SetCVal

instance Delta Cδ where
  type Val Cδ = SetCVal
  type Δ Cδ μ = (Ord (Addr μ), Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ))
  lit :: (Δ Cδ μ) => P Cδ -> Lit -> Val Cδ μ
  lit P = SetCVal . ssingleton . LitC
  clo :: (Δ Cδ μ) => P Cδ -> Clo μ -> Val Cδ μ
  clo P = SetCVal . ssingleton . CloC
  op :: (Δ Cδ μ) => P Cδ -> Op -> Val Cδ μ -> Val Cδ μ
  op P Add1     = update runSetCValL $ cmap (LitC . I . (+  1   )) . cextend (useMaybeSet . coerceI *. coerceLitC)
  op P Sub1     = update runSetCValL $ cmap (LitC . I . (+  (-1))) . cextend (useMaybeSet . coerceI *. coerceLitC)
  op P IsNonNeg = update runSetCValL $ cmap (LitC . B . (>= 0   )) . cextend (useMaybeSet . coerceI *. coerceLitC)
  elimBool :: (Δ Cδ μ) => P Cδ -> Val Cδ μ -> Set Bool
  elimBool P = cextend (useMaybeSet . coerceB *. coerceLitC) . runSetCVal
  elimClo :: (Δ Cδ μ) => P Cδ -> Val Cδ μ -> Set (Clo μ)
  elimClo P = cextend (useMaybeSet . coerceCloC) . runSetCVal

--------------
-- Abstract --
--------------

data Aδ
aδ :: P Aδ
aδ = P

data AVal μ = IA | BA | CloA (Clo μ)
deriving instance (Eq (LexicalTime μ Ψ), Eq (DynamicTime μ Ψ)) => Eq (AVal μ)
deriving instance (Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ)) => Ord (AVal μ)

coerceIA :: AVal μ -> Maybe ()
coerceIA IA = Just ()
coerceIA _ = Nothing
coerceBA :: AVal μ -> Maybe ()
coerceBA BA = Just ()
coerceBA _ = Nothing
coerceCloA :: AVal μ -> Maybe (Clo μ)
coerceCloA (CloA c) = Just c
coerceCloA _ = Nothing

denoteIA :: Set Bool
denoteIA = ssingleton True \/ ssingleton False

newtype SetAVal μ = SetAVal { runSetAVal :: Set (AVal μ) }
runSetAValL :: Lens (SetAVal μ) (Set (AVal μ))
runSetAValL = isoLens runSetAVal SetAVal

instance Delta Aδ where
  type Val Aδ = SetAVal
  type Δ Aδ μ = (Ord (Addr μ), Ord (LexicalTime μ Ψ), Ord (DynamicTime μ Ψ))
  lit :: (Δ Aδ μ) => P Aδ -> Lit -> Val Aδ μ
  lit P (I _) = SetAVal $ ssingleton IA
  lit P (B _) = SetAVal $ ssingleton BA
  clo :: (Δ Aδ μ) => P Aδ -> Clo μ -> Val Aδ μ
  clo P = SetAVal . ssingleton . CloA
  op :: (Δ Aδ μ) => P Aδ -> Op -> Val Aδ μ -> Val Aδ μ
  op P Add1     = update runSetAValL $ cmap (const IA) . cextend (useMaybeSet . coerceIA)
  op P Sub1     = update runSetAValL $ cmap (const IA) . cextend (useMaybeSet . coerceIA)
  op P IsNonNeg = update runSetAValL $ cmap (const BA) . cextend (useMaybeSet . coerceIA)
  elimBool :: (Δ Aδ μ) => P Aδ -> Val Aδ μ -> Set Bool
  elimBool P = cextend (const denoteIA *.~ useMaybeSet . coerceBA) . runSetAVal
  elimClo :: (Δ Aδ μ) => P Aδ -> Val Aδ μ -> Set (Clo μ)
  elimClo P = cextend (useMaybeSet . coerceCloA) . runSetAVal
