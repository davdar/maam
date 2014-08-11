module Lang.CPS.Instances.Delta.Abstract where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

data Aδ
aδ :: P Aδ
aδ = P

data AVal μ = IA | BA | CloA (Clo μ)
  deriving (Eq, Ord)
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
  type Δ Aδ μ = Ord (Addr μ)
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
