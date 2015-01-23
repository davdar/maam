module Lang.CPS.Val where

import FP
import Lang.Common
import Lang.CPS.StateSpace

-- Concrete
data CVal lτ dτ ψ = LitC Lit | CloC (Clo lτ dτ ψ) | BotC
  deriving (Eq, Ord)
makePrisms ''CVal

instance (Ord (dτ ψ), Ord (lτ ψ)) => Val lτ dτ ψ (CVal lτ dτ ψ) where
  lit :: Lit -> CVal lτ dτ ψ
  lit = LitC
  clo :: Clo lτ dτ ψ -> CVal lτ dτ ψ
  clo = CloC
  op :: Op -> CVal lτ dτ ψ -> CVal lτ dτ ψ
  op Add1 (LitC (I n)) = LitC $ I $ n+1
  op Sub1 (LitC (I n)) = LitC $ I $ n-1
  op IsNonNeg (LitC (I n)) = LitC $ B $ n >= 0
  op _ _ = BotC
  elimBool :: CVal lτ dτ ψ -> Set Bool
  elimBool (LitC (B b)) = singleton b
  elimBool _ = empty
  elimClo :: CVal lτ dτ ψ -> Set (Clo lτ dτ ψ)
  elimClo (CloC c) = singleton c
  elimClo _ = empty

-- Abstract
data AVal lτ dτ ψ = LitA Lit | IA | BA | CloA (Clo lτ dτ ψ) | BotA
  deriving (Eq, Ord)
makePrisms ''AVal

instance (Ord (lτ ψ), Ord (dτ ψ)) =>  Val lτ dτ ψ (AVal lτ dτ ψ) where
  lit :: Lit -> AVal lτ dτ ψ
  lit = LitA
  clo :: Clo lτ dτ ψ -> AVal lτ dτ ψ
  clo = CloA
  op :: Op -> AVal lτ dτ ψ -> AVal lτ dτ ψ
  op Add1 (LitA (I _)) = IA
  op Add1 IA = IA
  op Sub1 (LitA (I _)) = IA
  op Sub1 IA = IA
  op IsNonNeg (LitA (I _)) = BA
  op IsNonNeg IA = BA
  op _ _ = BotA
  elimBool :: AVal lτ dτ ψ -> Set Bool
  elimBool (LitA (B b)) = singleton b
  elimBool BA = fromList [True, False]
  elimBool _ = empty
  elimClo :: AVal lτ dτ ψ -> Set (Clo lτ dτ ψ)
  elimClo (CloA c) = singleton c
  elimClo _ = empty

-- Lifting to Powerset
newtype Power val lτ dτ ψ = Power { runPower :: Set (val lτ dτ ψ) }
  deriving 
    ( Eq, Ord, PartialOrder, JoinLattice
    , Iterable (val lτ dτ ψ), Container (val lτ dτ ψ), SetLike (val lτ dτ ψ)
    )

instance (Ord (dτ ψ), Ord (lτ ψ)) => Val lτ dτ ψ (Power CVal lτ dτ ψ) where
  lit = Power . singleton . lit
  clo = Power . singleton . clo
  op o = Power . setMap (op o) . runPower
  elimBool = extend elimBool . runPower
  elimClo = extend elimClo . runPower

instance (Ord (dτ ψ), Ord (lτ ψ)) => Val lτ dτ ψ (Power AVal lτ dτ ψ) where
  lit = Power . singleton . lit
  clo = Power . singleton . clo
  op o = Power . setMap (op o) . runPower
  elimBool = extend elimBool . runPower
  elimClo = extend elimClo . runPower
