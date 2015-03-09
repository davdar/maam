module Lang.Hask.ValConcrete where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon

data CVal lτ dτ =
    CLit Literal
  | CData (Data lτ dτ)
  | CDataAny DataCon
  | CFunClo (FunClo lτ dτ)
  | CThunkClo (ThunkClo lτ dτ)
  | CForced (OCVal lτ dτ)
  | CRef (Ref lτ dτ)
  | CRefAny
  | CKonClo (KonClo lτ dτ)
  | CKonMemoClo (KonMemoClo lτ dτ CVal)
  deriving (Eq, Ord)
data OCVal lτ dτ = Bot | Top | Pos (CVal lτ dτ) | Neg (CVal lτ dτ)
  deriving (Eq, Ord)
newtype PCVal lτ dτ = PCVal { unPCVal :: Set (OCVal lτ dτ) }

instance (Ord lτ, Ord dτ) => Val OCVal lτ dτ where

  botI :: OCVal lτ dτ
  botI = Bot

  neg :: OCVal lτ dτ -> OCVal lτ dτ
  neg Bot = Top
  neg Top = Bot
  neg (Pos v) = Neg v
  neg (Neg v) = Pos v

  litI :: Literal -> OCVal lτ dτ
  litI = Pos . CLit

  litTestE :: Literal -> OCVal lτ dτ -> Set Bool
  litTestE _ Bot = empty
  litTestE _ Top = fromList [False, True]
  litTestE l (Pos (CLit l')) | l == l' = singleton True
  litTestE _ (Pos _) = singleton False
  litTestE l (Neg v) = setMap not $ litTestE l $ Pos v

  dataI :: Data lτ dτ -> OCVal lτ dτ
  dataI = Pos . CData

  dataAnyI :: DataCon -> OCVal lτ dτ
  dataAnyI = Pos . CDataAny

  dataE :: OCVal lτ dτ -> Maybe (Set (Data lτ dτ))
  dataE Bot = Just empty
  dataE Top = Nothing
  dataE (Pos (CData d)) = Just $ singleton d
  dataE (Pos (CDataAny _)) = Nothing
  dataE (Pos _) = Just empty
  dataE (Neg _) = Nothing

  funCloI :: FunClo lτ dτ -> OCVal lτ dτ
  funCloI = Pos . CFunClo

  funCloE :: OCVal lτ dτ -> Maybe (Set (FunClo lτ dτ))
  funCloE Bot = Just empty
  funCloE Top = Nothing
  funCloE (Pos (CFunClo f)) = Just $ singleton f
  funCloE (Pos _) = Just empty
  funCloE (Neg _) = Nothing

  thunkCloI :: ThunkClo lτ dτ -> OCVal lτ dτ
  thunkCloI = Pos . CThunkClo

  thunkCloE :: OCVal lτ dτ -> Maybe (Set (ThunkClo lτ dτ))
  thunkCloE Bot = Just empty
  thunkCloE Top = Nothing
  thunkCloE (Pos (CThunkClo t)) = Just $ singleton t
  thunkCloE (Pos _) = Just empty
  thunkCloE (Neg _) = Nothing

  forcedI :: OCVal lτ dτ -> OCVal lτ dτ
  forcedI = Pos . CForced

  forcedE :: OCVal lτ dτ -> Maybe (Set (OCVal lτ dτ))
  forcedE Bot = Just empty
  forcedE Top = Nothing
  forcedE (Pos (CForced v)) = Just $ singleton v
  forcedE (Pos _) = Just empty
  forcedE (Neg _) = Nothing

  refI :: Ref lτ dτ -> OCVal lτ dτ
  refI = Pos . CRef

  refAnyI :: OCVal lτ dτ
  refAnyI = Pos CRefAny

  refE :: OCVal lτ dτ -> Maybe (Set (Ref lτ dτ))

  konCloI :: KonClo lτ dτ -> OCVal lτ dτ

  konCloE :: OCVal lτ dτ -> Maybe (Set (KonClo lτ dτ))

  konMemoCloI :: KonMemoClo lτ dτ OCVal -> OCVal lτ dτ

  konMemoCloE :: OCVal lτ dτ -> Maybe (Set (KonMemoClo lτ dτ OCVal))

