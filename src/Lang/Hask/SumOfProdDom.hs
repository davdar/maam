module Lang.Hask.SumOfProdDom where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon
import Lang.Hask.SetWithTop

data IValProj a = 
    IConcrete (Set a)
  | IPredicate (a -> Bool)

newtype SumOfProd ν lτ dτ = SumOfProd { unSumOfProd :: Set (Set (ν lτ dτ)) }
makePrettyUnion ''SumOfProd

injectSOP :: (Ord (ν lτ dτ)) => ν lτ dτ -> SumOfProd ν lτ dτ
injectSOP = SumOfProd . singleton . singleton

mapSOP :: (Ord (ν lτ dτ)) => (ν lτ dτ -> ν lτ dτ) -> SumOfProd ν lτ dτ -> SumOfProd ν lτ dτ
mapSOP f (SumOfProd sps) = SumOfProd $ setMap (setMap f) sps

partition :: [IValProj a] -> ([SetWithTop a], [a -> Bool])
partition = iter ff ([], [])
  where
    ff (IConcrete c) (cs, ps) = (SetNotTop c : cs, ps)
    ff (IPredicate p) (cs, ps) = (cs, p : ps)

partitionMeet :: [IValProj a] -> ListWithTop a
partitionMeet xs = do
  let (cs, ps) = partition xs
      c = meets cs
      p = joins ps
  case c of
    SetTop -> if isNil ps then mzero else mtop
    SetNotTop candidates -> do
      candidate <- mlist $ toList candidates
      guard $ p candidate
      return candidate

project :: (Ord a) => (ν lτ dτ -> IValProj a) -> SumOfProd ν lτ dτ -> SetWithTop a
project p v = fromListWithTop $ partitionMeet *$ mlist $ map (map p . toList) $ toList $ unSumOfProd v

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

instance (Ord (ν lτ dτ), Neg (ν lτ dτ)) => Neg (SumOfProd ν lτ dτ) where
  neg :: SumOfProd ν lτ dτ -> SumOfProd ν lτ dτ
  neg (SumOfProd xss) = SumOfProd $ setBigProduct $ setMap (setMap neg) xss

instance (Ord lτ, Ord dτ, Ord (ν lτ dτ), Val lτ dτ IValProj ν) => Val lτ dτ SetWithTop (SumOfProd ν) where
  botI :: SumOfProd ν lτ dτ
  botI = injectSOP botI

  litI :: Literal -> SumOfProd ν lτ dτ
  litI = injectSOP . litI

  litTestE :: Literal -> SumOfProd ν lτ dτ -> SetWithTop Bool
  litTestE = project . litTestE

  dataI :: Data lτ dτ -> SumOfProd ν lτ dτ
  dataI = injectSOP . dataI

  dataAnyI :: DataCon -> SumOfProd ν lτ dτ
  dataAnyI = injectSOP . dataAnyI

  dataE :: SumOfProd ν lτ dτ -> SetWithTop (Data lτ dτ)
  dataE = project dataE

  funCloI :: FunClo lτ dτ -> SumOfProd ν lτ dτ
  funCloI = injectSOP . funCloI

  funCloE :: SumOfProd ν lτ dτ -> SetWithTop (FunClo lτ dτ)
  funCloE = project funCloE

  thunkCloI :: ThunkClo lτ dτ -> SumOfProd ν lτ dτ
  thunkCloI = injectSOP . thunkCloI

  thunkCloE :: SumOfProd ν lτ dτ -> SetWithTop (ThunkClo lτ dτ)
  thunkCloE = project thunkCloE

  forcedI :: Forced lτ dτ -> SumOfProd ν lτ dτ
  forcedI = injectSOP . forcedI

  forcedE :: SumOfProd ν lτ dτ -> SetWithTop (Forced lτ dτ)
  forcedE = project forcedE

  refI :: Ref lτ dτ -> SumOfProd ν lτ dτ
  refI = injectSOP . refI

  refAnyI :: SumOfProd ν lτ dτ
  refAnyI = injectSOP refAnyI

  refE :: SumOfProd ν lτ dτ -> SetWithTop (Ref lτ dτ)
  refE = project refE

  konCloI :: KonClo lτ dτ -> SumOfProd ν lτ dτ
  konCloI = injectSOP . konCloI

  konCloE :: SumOfProd ν lτ dτ -> SetWithTop (KonClo lτ dτ)
  konCloE = project konCloE

  konMemoCloI :: KonMemoClo lτ dτ -> SumOfProd ν lτ dτ
  konMemoCloI = injectSOP . konMemoCloI

  konMemoCloE :: SumOfProd ν lτ dτ -> SetWithTop (KonMemoClo lτ dτ)
  konMemoCloE = project konMemoCloE
