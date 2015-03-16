module Lang.Hask.ValConcrete where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon

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
makePrettySum ''CVal
cν :: P CVal
cν = P

data OCVal lτ dτ = Pos (CVal lτ dτ) | Neg (CVal lτ dτ)
  deriving (Eq, Ord)
makePrettySum ''OCVal

discreteE :: (Ord b) => Prism (CVal lτ dτ) b -> OCVal lτ dτ -> ConstructiveClassical b
discreteE l (Pos v) = case view l v of
  Just x -> Constructive $ single x
  Nothing -> Constructive empty
discreteE l (Neg v) = case view l v of
  Just x -> Classical $ \ x' -> x /= x'
  Nothing -> Classical $ const True

instance Neg (OCVal lτ dτ) where
  neg :: OCVal lτ dτ -> OCVal lτ dτ
  neg (Pos v) = Neg v
  neg (Neg v) = Pos v

instance (Ord lτ, Ord dτ) => Val lτ dτ ConstructiveClassical OCVal where
  botI :: OCVal lτ dτ
  botI = Pos CBot

  litI :: Literal -> OCVal lτ dτ
  litI = Pos . CLit

  litTestE :: Literal -> OCVal lτ dτ -> ConstructiveClassical Bool
  litTestE l (Pos (CLit l')) 
    | l == l' = Constructive $ single True
    | otherwise = Constructive $ single False
  litTestE _ (Pos _) = Constructive empty
  litTestE l (Neg (CLit l')) 
    | l == l' = Constructive $ single False
    | otherwise = Constructive $ fromList [False, True]
  litTestE _ (Neg _) = Constructive $ fromList [False, True]

  dataI :: Data lτ dτ -> OCVal lτ dτ
  dataI = Pos . CData

  dataAnyI :: DataCon -> OCVal lτ dτ
  dataAnyI = Pos . CDataAny

  dataE :: OCVal lτ dτ -> ConstructiveClassical (Data lτ dτ)
  dataE (Pos (CData d)) = Constructive $ single d
  dataE (Pos (CDataAny con)) = Classical $ \ d -> dataCon d == con
  dataE (Pos _) = Constructive empty
  dataE (Neg (CData d)) = Classical $ \ d' -> d /= d'
  dataE (Neg (CDataAny con)) = Classical $ \ d -> dataCon d /= con
  dataE (Neg _) = Classical $ const True

  funCloI :: FunClo lτ dτ -> OCVal lτ dτ
  funCloI = Pos . CFunClo

  funCloE :: OCVal lτ dτ -> ConstructiveClassical (FunClo lτ dτ)
  funCloE = discreteE cFunCloL

  thunkCloI :: ThunkClo lτ dτ -> OCVal lτ dτ
  thunkCloI = Pos . CThunkClo

  thunkCloE :: OCVal lτ dτ -> ConstructiveClassical (ThunkClo lτ dτ)
  thunkCloE = discreteE cThunkCloL

  forcedI :: Forced lτ dτ -> OCVal lτ dτ
  forcedI = Pos . CForced

  forcedE :: OCVal lτ dτ -> ConstructiveClassical (Forced lτ dτ)
  forcedE = discreteE cForcedL

  refI :: Ref lτ dτ -> OCVal lτ dτ
  refI = Pos . CRef

  refAnyI :: OCVal lτ dτ
  refAnyI = Pos CRefAny

  refE :: OCVal lτ dτ -> ConstructiveClassical (Ref lτ dτ)
  refE (Pos (CRef r)) = Constructive $ single r
  refE (Pos CRefAny) = Classical $ const True
  refE (Pos _) = Constructive empty
  refE (Neg (CRef r)) = Classical $ \ r' -> r /= r'
  refE (Neg CRefAny) = Constructive empty
  refE (Neg _) = Classical $ const True

  konCloI :: KonClo lτ dτ -> OCVal lτ dτ
  konCloI = Pos . CKonClo

  konCloE :: OCVal lτ dτ -> ConstructiveClassical (KonClo lτ dτ)
  konCloE = discreteE cKonCloL

  konMemoCloI :: KonMemoClo lτ dτ -> OCVal lτ dτ
  konMemoCloI = Pos . CKonMemoClo

  konMemoCloE :: OCVal lτ dτ -> ConstructiveClassical (KonMemoClo lτ dτ)
  konMemoCloE = discreteE cKonMemoCloL
