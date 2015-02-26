module Lang.LamIf.Val where

import FP
import Lang.LamIf.StateSpace
import Lang.LamIf.Syntax

-- Concrete
data CVal lτ dτ ψ = LitC Lit | CloC (Clo lτ dτ ψ) | BotC
  deriving (Eq, Ord)
makePrisms ''CVal

instance (Eq (lτ ψ), Eq (dτ ψ)) => PartialOrder (CVal lτ dτ ψ) where
  pcompare BotC _ = PLT
  pcompare _ BotC = PGT
  pcompare v1 v2 | v1 == v2  = PEQ
                 | otherwise = PUN

instance (Ord (dτ ψ), Ord (lτ ψ)) => Val lτ dτ ψ (CVal lτ dτ ψ) where
  lit :: Lit -> CVal lτ dτ ψ
  lit = LitC
  clo :: Clo lτ dτ ψ -> CVal lτ dτ ψ
  clo = CloC
  binop :: BinOp -> CVal lτ dτ ψ -> CVal lτ dτ ψ -> CVal lτ dτ ψ
  binop Add (LitC (I n1)) (LitC (I n2)) = LitC $ I $ n1 + n2
  binop Sub (LitC (I n1)) (LitC (I n2)) = LitC $ I $ n1 - n2
  binop GTE (LitC (I n1)) (LitC (I n2)) = LitC $ B $ n1 >= n2
  binop _ _ _ = BotC
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

instance (Eq (lτ ψ), Eq (dτ ψ)) => PartialOrder (AVal lτ dτ ψ) where
  pcompare BotA _ = PLT
  pcompare _ BotA = PGT
  pcompare (LitA (I _)) IA = PLT
  pcompare IA (LitA (I _)) = PGT
  pcompare (LitA (B _)) BA = PLT
  pcompare BA (LitA (B _)) = PGT
  pcompare v1 v2 | v1 == v2 = PEQ
                 | otherwise = PUN

instance (Ord (lτ ψ), Ord (dτ ψ)) =>  Val lτ dτ ψ (AVal lτ dτ ψ) where
  lit :: Lit -> AVal lτ dτ ψ
  lit = LitA
  clo :: Clo lτ dτ ψ -> AVal lτ dτ ψ
  clo = CloA
  binop :: BinOp -> AVal lτ dτ ψ -> AVal lτ dτ ψ -> AVal lτ dτ ψ
  binop Add v1 v2 | v1 <~ IA && v2 <~ IA = IA
  binop Sub v1 v2 | v1 <~ IA && v2 <~ IA = IA
  binop GTE v1 v2 | v1 <~ IA && v2 <~ IA = BA
  binop _ _ _ = BotA
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
  binop o vP1 vP2 = Power $ do
    v1 <- runPower vP1
    v2 <- runPower vP2
    singleton $ binop o v1 v2
  elimBool = extend elimBool . runPower
  elimClo = extend elimClo . runPower

instance (Ord (dτ ψ), Ord (lτ ψ)) => Val lτ dτ ψ (Power AVal lτ dτ ψ) where
  lit = Power . singleton . lit
  clo = Power . singleton . clo
  binop o vP1 vP2 = Power $ do
    v1 <- runPower vP1
    v2 <- runPower vP2
    singleton $ binop o v1 v2
  elimBool = extend elimBool . runPower
  elimClo = extend elimClo . runPower
