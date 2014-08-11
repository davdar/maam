module Lang.CPS.Instances.Delta.Concrete where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

data Cδ
cδ :: P Cδ
cδ = P

data CVal μ = LitC Lit | CloC (Clo μ)
  deriving (Eq, Ord)
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
  type Δ Cδ μ = Ord (Addr μ)
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
