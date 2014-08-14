module Lang.CPS.Instances.Delta.Abstract where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

data Aδ
aδ :: P Aδ
aδ = P

data AVal μ ψ = IA | BA | CloA (Clo μ ψ)
deriving instance (Eq (LexicalTime μ ψ), Eq (DynamicTime μ ψ)) => Eq (AVal μ ψ)
deriving instance (Ord (LexicalTime μ ψ), Ord (DynamicTime μ ψ)) => Ord (AVal μ ψ)

coerceIA :: AVal μ ψ -> Maybe ()
coerceIA IA = Just ()
coerceIA _ = Nothing
coerceBA :: AVal μ ψ -> Maybe ()
coerceBA BA = Just ()
coerceBA _ = Nothing
coerceCloA :: AVal μ ψ -> Maybe (Clo μ ψ)
coerceCloA (CloA c) = Just c
coerceCloA _ = Nothing

denoteIA :: Set Bool
denoteIA = ssingleton True \/ ssingleton False

newtype SetAVal μ ψ = SetAVal { runSetAVal :: Set (AVal μ ψ) }
runSetAValL :: Lens (SetAVal μ ψ) (Set (AVal μ ψ))
runSetAValL = isoLens runSetAVal SetAVal

instance Delta Aδ where
  type Val Aδ = SetAVal
  type Δ Aδ μ ψ = (Ord (Addr μ ψ), Ord (LexicalTime μ ψ), Ord (DynamicTime μ ψ))
  lit :: (Δ Aδ μ ψ) => P Aδ -> Lit -> Val Aδ μ ψ
  lit P (I _) = SetAVal $ ssingleton IA
  lit P (B _) = SetAVal $ ssingleton BA
  clo :: (Δ Aδ μ ψ) => P Aδ -> Clo μ ψ -> Val Aδ μ ψ
  clo P = SetAVal . ssingleton . CloA
  op :: (Δ Aδ μ ψ) => P Aδ -> Op -> Val Aδ μ ψ -> Val Aδ μ ψ
  op P Add1     = update runSetAValL $ cmap (const IA) . cextend (useMaybeSet . coerceIA)
  op P Sub1     = update runSetAValL $ cmap (const IA) . cextend (useMaybeSet . coerceIA)
  op P IsNonNeg = update runSetAValL $ cmap (const BA) . cextend (useMaybeSet . coerceIA)
  elimBool :: (Δ Aδ μ ψ) => P Aδ -> Val Aδ μ ψ -> Set Bool
  elimBool P = cextend (const denoteIA *.~ useMaybeSet . coerceBA) . runSetAVal
  elimClo :: (Δ Aδ μ ψ) => P Aδ -> Val Aδ μ ψ -> Set (Clo μ ψ)
  elimClo P = cextend (useMaybeSet . coerceCloA) . runSetAVal
