module Lang.Hask.ValConcrete where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon
import Lang.Hask.SumOfProdDom

data CVal lτ dτ =
    CBot
  | CLit Literal
  | CData (Data lτ dτ)
  | CDataAny DataCon
  | CFunClo (FunClo lτ dτ)
  | CThunkClo (ThunkClo lτ dτ)
  | CForced (Forced lτ dτ)
  | CRef (Ref lτ dτ)
  | CRefAny
  | CKonClo (KonClo lτ dτ)
  | CKonMemoClo (KonMemoClo lτ dτ)
  deriving (Eq, Ord)
makePrisms ''CVal

data OCVal lτ dτ = Pos (CVal lτ dτ) | Neg (CVal lτ dτ)
  deriving (Eq, Ord)

discreteE :: (Ord b) => Prism (CVal lτ dτ) b -> OCVal lτ dτ -> IValProj b
discreteE l (Pos v) = case view l v of
  Just x -> IConcrete $ singleton x
  Nothing -> IConcrete empty
discreteE l (Neg v) = case view l v of
  Just x -> IPredicate $ \ x' -> x /= x'
  Nothing -> IPredicate $ const True

instance Neg (OCVal lτ dτ) where
  neg :: OCVal lτ dτ -> OCVal lτ dτ
  neg (Pos v) = Neg v
  neg (Neg v) = Pos v

instance (Ord lτ, Ord dτ) => Val lτ dτ IValProj OCVal where
  botI :: OCVal lτ dτ
  botI = Pos CBot

  litI :: Literal -> OCVal lτ dτ
  litI = Pos . CLit

  litTestE :: Literal -> OCVal lτ dτ -> IValProj Bool
  litTestE l (Pos (CLit l')) 
    | l == l' = IConcrete $ singleton True
    | otherwise = IConcrete $ singleton False
  litTestE _ (Pos _) = IConcrete empty
  litTestE l (Neg (CLit l')) 
    | l == l' = IConcrete $ singleton False
    | otherwise = IConcrete $ fromList [False, True]
  litTestE _ (Neg _) = IConcrete $ fromList [False, True]

  dataI :: Data lτ dτ -> OCVal lτ dτ
  dataI = Pos . CData

  dataAnyI :: DataCon -> OCVal lτ dτ
  dataAnyI = Pos . CDataAny

  dataE :: OCVal lτ dτ -> IValProj (Data lτ dτ)
  dataE (Pos (CData d)) = IConcrete $ singleton d
  dataE (Pos (CDataAny con)) = IPredicate $ \ d -> dataCon d == con
  dataE (Pos _) = IConcrete empty
  dataE (Neg (CData d)) = IPredicate $ \ d' -> d /= d'
  dataE (Neg (CDataAny con)) = IPredicate $ \ d -> dataCon d /= con
  dataE (Neg _) = IPredicate $ const True

  funCloI :: FunClo lτ dτ -> OCVal lτ dτ
  funCloI = Pos . CFunClo

  funCloE :: OCVal lτ dτ -> IValProj (FunClo lτ dτ)
  funCloE = discreteE cFunCloL

  thunkCloI :: ThunkClo lτ dτ -> OCVal lτ dτ
  thunkCloI = Pos . CThunkClo

  thunkCloE :: OCVal lτ dτ -> IValProj (ThunkClo lτ dτ)
  thunkCloE = discreteE cThunkCloL

  forcedI :: Forced lτ dτ -> OCVal lτ dτ
  forcedI = Pos . CForced

  forcedE :: OCVal lτ dτ -> IValProj (Forced lτ dτ)
  forcedE = discreteE cForcedL

  refI :: Ref lτ dτ -> OCVal lτ dτ
  refI = Pos . CRef

  refAnyI :: OCVal lτ dτ
  refAnyI = Pos CRefAny

  refE :: OCVal lτ dτ -> IValProj (Ref lτ dτ)
  refE (Pos (CRef r)) = IConcrete $ singleton r
  refE (Pos CRefAny) = IPredicate $ const True
  refE (Pos _) = IConcrete empty
  refE (Neg (CRef r)) = IPredicate $ \ r' -> r /= r'
  refE (Neg CRefAny) = IConcrete empty
  refE (Neg _) = IPredicate $ const True

  konCloI :: KonClo lτ dτ -> OCVal lτ dτ
  konCloI = Pos . CKonClo

  konCloE :: OCVal lτ dτ -> IValProj (KonClo lτ dτ)
  konCloE = discreteE cKonCloL

  konMemoCloI :: KonMemoClo lτ dτ -> OCVal lτ dτ
  konMemoCloI = Pos . CKonMemoClo

  konMemoCloE :: OCVal lτ dτ -> IValProj (KonMemoClo lτ dτ)
  konMemoCloE = discreteE cKonMemoCloL
