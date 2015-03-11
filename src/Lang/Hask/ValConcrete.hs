module Lang.Hask.ValConcrete where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon
import Lang.Hask.SumOfProdDom

data CVal ν lτ dτ =
    CBot
  | CLit Literal
  | CData (Data lτ dτ)
  | CDataAny DataCon
  | CFunClo (FunClo lτ dτ)
  | CThunkClo (ThunkClo lτ dτ)
  | CForced (ν lτ dτ)
  | CRef (Ref lτ dτ)
  | CRefAny
  | CKonClo (KonClo lτ dτ)
  | CKonMemoClo (KonMemoClo lτ dτ ν)
  deriving (Eq, Ord)
makePrisms ''CVal

data OCVal ν lτ dτ = Pos (CVal ν lτ dτ) | Neg (CVal ν lτ dτ)
  deriving (Eq, Ord)

discreteE :: (Ord b) => Prism (CVal ν lτ dτ) b -> OCVal ν lτ dτ -> IValProj b
discreteE l (Pos v) = case coerce l v of
  Just x -> IConcrete $ singleton x
  Nothing -> IConcrete empty
discreteE l (Neg v) = case coerce l v of
  Just x -> IPredicate $ \ x' -> x /= x'
  Nothing -> IPredicate $ const True

instance (Ord lτ, Ord dτ) => Val lτ dτ IValProj (OCVal ν) where
  botI :: OCVal ν lτ dτ
  botI = Pos CBot

  neg :: OCVal ν lτ dτ -> OCVal ν lτ dτ
  neg (Pos v) = Neg v
  neg (Neg v) = Pos v

  litI :: Literal -> OCVal ν lτ dτ
  litI = Pos . CLit

  litTestE :: Literal -> OCVal ν lτ dτ -> IValProj Bool
  litTestE l (Pos (CLit l')) 
    | l == l' = IConcrete $ singleton True
    | otherwise = IConcrete $ singleton False
  litTestE _ (Pos _) = IConcrete empty
  litTestE l (Neg (CLit l')) 
    | l == l' = IConcrete $ singleton False
    | otherwise = IConcrete $ fromList [False, True]
  litTestE _ (Neg _) = IConcrete $ fromList [False, True]

  dataI :: Data lτ dτ -> OCVal ν lτ dτ
  dataI = Pos . CData

  dataAnyI :: DataCon -> OCVal ν lτ dτ
  dataAnyI = Pos . CDataAny

  dataE :: OCVal ν lτ dτ -> IValProj (Data lτ dτ)
  dataE (Pos (CData d)) = IConcrete $ singleton d
  dataE (Pos (CDataAny con)) = IPredicate $ \ d -> dataCon d == con
  dataE (Pos _) = IConcrete empty
  dataE (Neg (CData d)) = IPredicate $ \ d' -> d /= d'
  dataE (Neg (CDataAny con)) = IPredicate $ \ d -> dataCon d /= con
  dataE (Neg _) = IPredicate $ const True

  funCloI :: FunClo lτ dτ -> OCVal ν lτ dτ
  funCloI = Pos . CFunClo

  funCloE :: OCVal ν lτ dτ -> IValProj (FunClo lτ dτ)
  funCloE = discreteE cFunCloL

  thunkCloI :: ThunkClo lτ dτ -> OCVal ν lτ dτ
  thunkCloI = Pos . CThunkClo

  thunkCloE :: OCVal ν lτ dτ -> IValProj (ThunkClo lτ dτ)
  thunkCloE = discreteE cThunkCloL

  forcedI :: ν lτ dτ -> OCVal ν lτ dτ
  forcedI = Pos . CForced

  forcedE :: OCVal ν lτ dτ -> IValProj (OCVal ν lτ dτ)
  forcedE = discreteE cForcedL

  refI :: Ref lτ dτ -> OCVal ν lτ dτ
  refI = Pos . CRef

  refAnyI :: OCVal ν lτ dτ
  refAnyI = Pos CRefAny

  refE :: OCVal ν lτ dτ -> IValProj (Ref lτ dτ)
  refE (Pos (CRef r)) = IConcrete $ singleton r
  refE (Pos CRefAny) = IPredicate $ const True
  refE (Pos _) = IConcrete empty
  refE (Neg (CRef r)) = IPredicate $ \ r' -> r /= r'
  refE (Neg CRefAny) = IConcrete empty
  refE (Neg _) = IPredicate $ const True

  konCloI :: KonClo lτ dτ -> OCVal ν lτ dτ
  konCloI = Pos . CKonClo

  konCloE :: OCVal ν lτ dτ -> IValProj (KonClo lτ dτ)
  konCloE = discreteE cKonCloL

  konMemoCloI :: KonMemoClo lτ dτ OCVal ν -> OCVal ν lτ dτ
  konMemoCloI = Pos . CKonMemoClo

  konMemoCloE :: OCVal ν lτ dτ -> IValProj (KonMemoClo lτ dτ OCVal ν)
  konMemoCloE = discreteE cKonMemoCloL
