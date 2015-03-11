module Lang.Hask.SumOfProdDom where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon

data IValProj a = 
    IConcrete (Set a)
  | IPredicate (a -> Bool)

newtype SumOfProd ν lτ dτ = SumOfProd { unSumOfProd :: Set (Set (ν lτ dτ)) }
makePrettyUnion ''SumOfProd

injectSOP :: (Ord (ν lτ dτ)) => ν lτ dτ -> SumOfProd ν lτ dτ
injectSOP = SumOfProd . singleton . singleton

mapSOP :: (Ord (ν lτ dτ)) => (ν lτ dτ -> ν lτ dτ) -> SumOfProd ν lτ dτ -> SumOfProd ν lτ dτ
mapSOP f (SumOfProd sps) = SumOfProd $ setMap (setMap f) sps


instance Bot (SumOfProd lτ dτ a) where
  bot = SumOfProd empty
instance Join (SumOfProd lτ dτ a) where
  SumOfProd sps₁ \/ SumOfProd sps₂ = SumOfProd $ sps₁ \/ sps₂
instance JoinLattice (SumOfProd lτ dτ a)

instance Meet (SumOfProd lτ dτ a) where
  SumOfProd sps₁ /\ SumOfProd sps₂ = SumOfProd $ do
    ps₁ <- sps₁
    ps₂ <- sps₂
    singleton $ ps₁ \/ ps₂

instance (Ord (ν lτ dτ), Val lτ dτ IValProj ν) => Val lτ dτ Set (SumOfProd ν) where
  botI :: SumOfProd ν lτ dτ
  botI = injectSOP botI

  neg :: SumOfProd ν lτ dτ -> SumOfProd ν lτ dτ

  litI :: Literal -> SumOfProd ν lτ dτ
  litI = injectSOP . litI

  litTestE :: Literal -> SumOfProd ν lτ dτ -> Set Bool

  dataI :: Data lτ dτ -> SumOfProd ν lτ dτ
  dataI = injectSOP . dataI

  dataAnyI :: DataCon -> SumOfProd ν lτ dτ
  dataAnyI = injectSOP . dataAnyI

  dataE :: SumOfProd ν lτ dτ -> Set (Data lτ dτ)

  funCloI :: FunClo lτ dτ -> SumOfProd ν lτ dτ
  funCloI = injectSOP . funCloI

  funCloE :: SumOfProd ν lτ dτ -> Set (FunClo lτ dτ)

  thunkCloI :: ThunkClo lτ dτ -> SumOfProd ν lτ dτ
  thunkCloI = injectSOP . thunkCloI

  thunkCloE :: SumOfProd ν lτ dτ -> Set (ThunkClo lτ dτ)

  forcedI :: SumOfProd ν lτ dτ -> SumOfProd ν lτ dτ
  forcedI = mapSOP forcedI

  forcedE :: SumOfProd ν lτ dτ -> Set (SumOfProd ν lτ dτ)

  refI :: Ref lτ dτ -> SumOfProd ν lτ dτ
  refI = injectSOP . refI

  refAnyI :: SumOfProd ν lτ dτ
  refAnyI = injectSOP refAnyI

  refE :: SumOfProd ν lτ dτ -> Set (Ref lτ dτ)

  konCloI :: KonClo lτ dτ -> SumOfProd ν lτ dτ
  konCloI = injectSOP . konCloI

  konCloE :: SumOfProd ν lτ dτ -> Set (KonClo lτ dτ)

  konMemoCloI :: KonMemoClo lτ dτ (SumOfProd ν) -> SumOfProd ν lτ dτ
  -- konMemoCloI = injectSOP . konMemoCloI

  konMemoCloE :: SumOfProd ν lτ dτ -> Set (KonMemoClo lτ dτ (SumOfProd ν))
