module Lang.CPS.Instances.Delta.Concrete where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

data Cδ
cδ :: P Cδ
cδ = P

data CVal μ ψ = LitC Lit | CloC (Clo μ ψ)
deriving instance (Eq (LexicalTime μ ψ), Eq (DynamicTime μ ψ)) => Eq (CVal μ ψ)
deriving instance (Ord (LexicalTime μ ψ), Ord (DynamicTime μ ψ)) => Ord (CVal μ ψ)

coerceLitC :: CVal μ ψ -> Maybe Lit
coerceLitC (LitC l) = Just l
coerceLitC _ = Nothing
coerceCloC :: CVal μ ψ -> Maybe (Clo μ ψ)
coerceCloC (CloC c) = Just c
coerceCloC _ = Nothing

newtype SetCVal μ ψ = SetCVal { runSetCVal :: Set (CVal μ ψ) }
runSetCValL :: Lens (SetCVal μ ψ) (Set (CVal μ ψ))
runSetCValL = isoLens runSetCVal SetCVal

instance Delta Cδ where
  type Val Cδ = SetCVal
  type Δ Cδ μ ψ = (Ord (Addr μ ψ), Ord (LexicalTime μ ψ), Ord (DynamicTime μ ψ))
  lit :: (Δ Cδ μ ψ) => P Cδ -> Lit -> Val Cδ μ ψ
  lit P = SetCVal . ssingleton . LitC
  clo :: (Δ Cδ μ ψ) => P Cδ -> Clo μ ψ -> Val Cδ μ ψ
  clo P = SetCVal . ssingleton . CloC
  op :: (Δ Cδ μ ψ) => P Cδ -> Op -> Val Cδ μ ψ -> Val Cδ μ ψ
  op P Add1     = update runSetCValL $ cmap (LitC . I . (+  1   )) . cextend (useMaybeSet . coerceI *. coerceLitC)
  op P Sub1     = update runSetCValL $ cmap (LitC . I . (+  (-1))) . cextend (useMaybeSet . coerceI *. coerceLitC)
  op P IsNonNeg = update runSetCValL $ cmap (LitC . B . (>= 0   )) . cextend (useMaybeSet . coerceI *. coerceLitC)
  elimBool :: (Δ Cδ μ ψ) => P Cδ -> Val Cδ μ ψ -> Set Bool
  elimBool P = cextend (useMaybeSet . coerceB *. coerceLitC) . runSetCVal
  elimClo :: (Δ Cδ μ ψ) => P Cδ -> Val Cδ μ ψ -> Set (Clo μ ψ)
  elimClo P = cextend (useMaybeSet . coerceCloC) . runSetCVal
