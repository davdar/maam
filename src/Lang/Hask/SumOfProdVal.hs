module Lang.Hask.SumOfProdVal where

import FP
import Lang.Hask.Semantics
import Literal
import DataCon

newtype SumOfProdVal ν lτ dτ = SumOfProdVal { unSumOfProdVal :: SumOfProd (ν lτ dτ) }
  deriving (Eq, Ord, Buildable (ν lτ dτ), Bot, Join, JoinLattice, Meet, Neg, Pretty)

sumOfProdValConcretize :: (Ord b) => (ν lτ dτ -> ConstructiveClassical b) -> SumOfProdVal ν lτ dτ -> SetWithTop b
sumOfProdValConcretize f = sumOfProdConcretize f . unSumOfProdVal

instance (Ord lτ, Ord dτ, Ord (ν lτ dτ), Val lτ dτ ConstructiveClassical ν) => Val lτ dτ SetWithTop (SumOfProdVal ν) where
  botI        :: SumOfProdVal ν lτ dτ                                  ; botI        = single botI
  litI        :: Literal -> SumOfProdVal ν lτ dτ                       ; litI        = single . litI
  litTestE    :: Literal -> SumOfProdVal ν lτ dτ -> SetWithTop Bool    ; litTestE    = sumOfProdValConcretize . litTestE
  dataI       :: Data lτ dτ -> SumOfProdVal ν lτ dτ                    ; dataI       = single . dataI
  dataAnyI    :: DataCon -> SumOfProdVal ν lτ dτ                       ; dataAnyI    = single . dataAnyI
  dataE       :: SumOfProdVal ν lτ dτ -> SetWithTop (Data lτ dτ)       ; dataE       = sumOfProdValConcretize dataE
  funCloI     :: FunClo lτ dτ -> SumOfProdVal ν lτ dτ                  ; funCloI     = single . funCloI
  funCloE     :: SumOfProdVal ν lτ dτ -> SetWithTop (FunClo lτ dτ)     ; funCloE     = sumOfProdValConcretize funCloE
  thunkCloI   :: ThunkClo lτ dτ -> SumOfProdVal ν lτ dτ                ; thunkCloI   = single . thunkCloI
  thunkCloE   :: SumOfProdVal ν lτ dτ -> SetWithTop (ThunkClo lτ dτ)   ; thunkCloE   = sumOfProdValConcretize thunkCloE
  forcedI     :: Forced lτ dτ -> SumOfProdVal ν lτ dτ                  ; forcedI     = single . forcedI
  forcedE     :: SumOfProdVal ν lτ dτ -> SetWithTop (Forced lτ dτ)     ; forcedE     = sumOfProdValConcretize forcedE
  refI        :: Ref lτ dτ -> SumOfProdVal ν lτ dτ                     ; refI        = single . refI
  refAnyI     :: SumOfProdVal ν lτ dτ                                  ; refAnyI     = single refAnyI
  refE        :: SumOfProdVal ν lτ dτ -> SetWithTop (Ref lτ dτ)        ; refE        = sumOfProdValConcretize refE
  konCloI     :: KonClo lτ dτ -> SumOfProdVal ν lτ dτ                  ; konCloI     = single . konCloI
  konCloE     :: SumOfProdVal ν lτ dτ -> SetWithTop (KonClo lτ dτ)     ; konCloE     = sumOfProdValConcretize konCloE
  konMemoCloI :: KonMemoClo lτ dτ -> SumOfProdVal ν lτ dτ              ; konMemoCloI = single . konMemoCloI
  konMemoCloE :: SumOfProdVal ν lτ dτ -> SetWithTop (KonMemoClo lτ dτ) ; konMemoCloE = sumOfProdValConcretize konMemoCloE
