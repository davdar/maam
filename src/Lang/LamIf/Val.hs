module Lang.LamIf.Val where

import FP
import Lang.LamIf.StateSpace
import Lang.LamIf.Syntax

-- Concrete
data CVal lτ dτ = LitC Lit | CloC (Clo lτ dτ) | BotC
  deriving (Eq, Ord)
makePrisms ''CVal

instance (Eq lτ, Eq dτ) => PartialOrder (CVal lτ dτ) where
  pcompare BotC _ = PLT
  pcompare _ BotC = PGT
  pcompare v1 v2 | v1 == v2  = PEQ
                 | otherwise = PUN

instance (Ord lτ, Ord dτ) => Val lτ dτ (CVal lτ dτ) where
  lit :: Lit -> CVal lτ dτ
  lit = LitC
  clo :: Clo lτ dτ -> CVal lτ dτ
  clo = CloC
  binop :: BinOp -> CVal lτ dτ -> CVal lτ dτ -> CVal lτ dτ
  binop Add (LitC (I n1)) (LitC (I n2)) = LitC $ I $ n1 + n2
  binop Sub (LitC (I n1)) (LitC (I n2)) = LitC $ I $ n1 - n2
  binop GTE (LitC (I n1)) (LitC (I n2)) = LitC $ B $ n1 >= n2
  binop _ _ _ = BotC
  elimBool :: CVal lτ dτ -> Set Bool
  elimBool (LitC (B b)) = single b
  elimBool _ = empty
  elimClo :: CVal lτ dτ -> Set (Clo lτ dτ)
  elimClo (CloC c) = single c
  elimClo _ = empty

-- Abstract
data AVal lτ dτ = LitA Lit | IA | BA | CloA (Clo lτ dτ) | BotA
  deriving (Eq, Ord)
makePrisms ''AVal

instance (Eq lτ, Eq dτ) => PartialOrder (AVal lτ dτ) where
  pcompare BotA _ = PLT
  pcompare _ BotA = PGT
  pcompare (LitA (I _)) IA = PLT
  pcompare IA (LitA (I _)) = PGT
  pcompare (LitA (B _)) BA = PLT
  pcompare BA (LitA (B _)) = PGT
  pcompare v1 v2 | v1 == v2 = PEQ
                 | otherwise = PUN

instance (Ord lτ, Ord dτ) =>  Val lτ dτ (AVal lτ dτ) where
  lit :: Lit -> AVal lτ dτ
  lit = LitA
  clo :: Clo lτ dτ -> AVal lτ dτ
  clo = CloA
  binop :: BinOp -> AVal lτ dτ -> AVal lτ dτ -> AVal lτ dτ
  binop Add v1 v2 | v1 ⊑ IA && v2 ⊑ IA = IA
  binop Sub v1 v2 | v1 ⊑ IA && v2 ⊑ IA = IA
  binop GTE v1 v2 | v1 ⊑ IA && v2 ⊑ IA = BA
  binop _ _ _ = BotA
  elimBool :: AVal lτ dτ -> Set Bool
  elimBool (LitA (B b)) = single b
  elimBool BA = fromList [True, False]
  elimBool _ = empty
  elimClo :: AVal lτ dτ -> Set (Clo lτ dτ)
  elimClo (CloA c) = single c
  elimClo _ = empty

-- Lifting to Powerset
newtype Power val lτ dτ = Power { runPower :: Set (val lτ dτ) }
  deriving 
    ( Eq, Ord, PartialOrder, Bot, Join, JoinLattice, Difference
    , Iterable (val lτ dτ), Container (val lτ dτ), Buildable (val lτ dτ)
    )

instance (Ord lτ, Ord dτ) => Val lτ dτ (Power CVal lτ dτ) where
  lit = Power . single . lit
  clo = Power . single . clo
  binop o vP1 vP2 = Power $ do
    v1 <- runPower vP1
    v2 <- runPower vP2
    single $ binop o v1 v2
  elimBool = extend elimBool . runPower
  elimClo = extend elimClo . runPower

instance (Ord lτ, Ord dτ) => Val lτ dτ (Power AVal lτ dτ) where
  lit = Power . single . lit
  clo = Power . single . clo
  binop o vP1 vP2 = Power $ do
    v1 <- runPower vP1
    v2 <- runPower vP2
    single $ binop o v1 v2
  elimBool = extend elimBool . runPower
  elimClo = extend elimClo . runPower
