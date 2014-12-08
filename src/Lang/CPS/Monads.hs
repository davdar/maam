module Lang.CPS.Monads where

import FP
import MAAM
import Lang.CPS.Val
import Lang.CPS.Semantics

-- Path Sensitive
data PSΣ val lτ dτ ψ = PSΣ
  { psρ :: Env lτ dτ ψ
  , pslτ :: Lτ lτ ψ
  , psσ :: Store val lτ dτ ψ
  , psdτ :: Dτ dτ ψ
  } deriving (Eq, Ord)
makeLenses ''PSΣ
instance HasLens (PSΣ val lτ dτ ψ) (Env lτ dτ ψ)       where view = psρL
instance HasLens (PSΣ val lτ dτ ψ) (Lτ lτ ψ)           where view = pslτL
instance HasLens (PSΣ val lτ dτ ψ) (Store val lτ dτ ψ) where view = psσL
instance HasLens (PSΣ val lτ dτ ψ) (Dτ dτ ψ)           where view = psdτL
instance (TimeC lτ, TimeC dτ) => Initial (PSΣ val lτ dτ Ψ) where
  initial = PSΣ initial initial initial initial

newtype FSPSς val lτ dτ ψ a = FSPSς { runFSPSς :: ListSet (a, PSΣ val lτ dτ ψ) }
  deriving (PartialOrder, JoinLattice)
instance Morphism2 (FSPSς val lτ dτ ψ) ((ID :.: ListSet) :.: (,) (PSΣ val lτ dτ ψ)) where
  morph2 = Compose . Compose . ID . map swap . runFSPSς
instance Morphism2 ((ID :.: ListSet) :.: (,) (PSΣ val lτ dτ ψ)) (FSPSς val lτ dτ ψ) where
  morph2 = FSPSς . map swap . runID . runCompose . runCompose
instance Isomorphism2 (FSPSς val lτ dτ ψ) ((ID :.: ListSet) :.: (,) (PSΣ val lτ dτ ψ)) where
instance (TimeC lτ, TimeC dτ) => Inject (FSPSς val lτ dτ Ψ) where
  inj = FSPSς . inj . (,initial)

newtype FSPS val lτ dτ ψ a = FSPS 
  { runFSPS :: IsoMonadStep (FSPSς val lτ dτ ψ) ((ID :.: ListSet) :.: (,) (PSΣ val lτ dτ ψ)) 
                 (StateT (PSΣ val lτ dτ ψ) (ListSetT ID)) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (PSΣ val lτ dτ ψ), MonadStateI (PSΣ val lτ dτ ψ), MonadState (PSΣ val lτ dτ ψ)
    , MonadStep (FSPSς val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (PSΣ val lτ dτ Ψ) (FSPSς val lτ dτ Ψ) (FSPS val lτ dτ Ψ) where

-- Path Insensitive
data PIΣ' lτ dτ ψ = PIΣ'
  { piρ :: Env lτ dτ ψ
  , pilτ :: Lτ lτ ψ
  , pidτ :: Dτ dτ ψ
  } deriving (Eq, Ord)
makeLenses ''PIΣ'
instance HasLens (PIΣ' lτ dτ ψ) (Env lτ dτ ψ) where view = piρL
instance HasLens (PIΣ' lτ dτ ψ) (Lτ lτ ψ)     where view = pilτL
instance HasLens (PIΣ' lτ dτ ψ) (Dτ dτ ψ)     where view = pidτL
instance (Initial (lτ ψ), Initial (dτ ψ)) => Initial (PIΣ' lτ dτ ψ) where
  initial = PIΣ' initial initial initial

data PIΣ val lτ dτ ψ = PIΣ
  { piΣ' :: PIΣ' lτ dτ ψ
  , piσ :: Store val lτ dτ ψ
  } deriving (Eq, Ord)
makeLenses ''PIΣ
instance Morphism (PIΣ val lτ dτ ψ) (PIΣ' lτ dτ ψ, Store val lτ dτ ψ) where morph (PIΣ ς' σ) = (ς', σ)
instance Morphism (PIΣ' lτ dτ ψ, Store val lτ dτ ψ) (PIΣ val lτ dτ ψ) where morph (ς', σ) = PIΣ ς' σ
instance Isomorphism (PIΣ val lτ dτ ψ) (PIΣ' lτ dτ ψ, Store val lτ dτ ψ) where
instance HasLens (PIΣ val lτ dτ ψ) (Env lτ dτ ψ)       where view = view <.> piΣ'L
instance HasLens (PIΣ val lτ dτ ψ) (Lτ lτ ψ)           where view = view <.> piΣ'L
instance HasLens (PIΣ val lτ dτ ψ) (Store val lτ dτ ψ) where view = piσL
instance HasLens (PIΣ val lτ dτ ψ) (Dτ dτ ψ)           where view = view <.> piΣ'L
instance (TimeC lτ, TimeC dτ) => Initial (PIΣ val lτ dτ Ψ) where
  initial = PIΣ initial initial

-- Flow Sensitive Path Insensitive
newtype FSPIς val lτ dτ ψ a = FSPIς { runFSPIς :: ListSet (a, PIΣ val lτ dτ ψ) }
  deriving (PartialOrder, JoinLattice)
instance Morphism2 (FSPIς val lτ dτ ψ) ((ListSet :.: ID :.: (,) (Store val lτ dτ ψ)) :.: (,) (PIΣ' lτ dτ ψ)) where
  morph2 = Compose . Compose . map (Compose . ID . (\ (a, PIΣ ς' σ) -> (σ, (ς', a)))) . runFSPIς
instance Morphism2 ((ListSet :.: ID :.: (,) (Store val lτ dτ ψ)) :.: (,) (PIΣ' lτ dτ ψ)) (FSPIς val lτ dτ ψ) where
  morph2 = FSPIς . map ((\ (σ, (ς', a)) -> (a, PIΣ ς' σ)) . runID . runCompose) . runCompose . runCompose
instance Isomorphism2 (FSPIς val lτ dτ ψ) ((ListSet :.: ID :.: (,) (Store val lτ dτ ψ)) :.: (,) (PIΣ' lτ dτ ψ)) where
instance (TimeC lτ, TimeC dτ) => Inject (FSPIς val lτ dτ Ψ) where
  inj = FSPIς . inj . (,initial)
newtype FSPI val lτ dτ ψ a = FSPI 
  { runFSPI :: IsoMonadStep (FSPIς val lτ dτ ψ) ((ListSet :.: ID :.: (,) (Store val lτ dτ ψ)) :.: (,) (PIΣ' lτ dτ ψ))
                 (AddStateT (PIΣ val lτ dτ ψ) (PIΣ' lτ dτ ψ) (ListSetT (StateT (Store val lτ dτ ψ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (PIΣ val lτ dτ ψ), MonadStateI (PIΣ val lτ dτ ψ), MonadState (PIΣ val lτ dτ ψ)
    , MonadStep (FSPIς val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (PIΣ val lτ dτ Ψ) (FSPIς val lτ dτ Ψ) (FSPI val lτ dτ Ψ) where

-- Flow Insensitive Path Insensitive
newtype FIPIς val lτ dτ ψ a = FIPIς { runFIPIς :: (ListSet (a, PIΣ' lτ dτ ψ), Store val lτ dτ ψ) }
  deriving (PartialOrder, JoinLattice)
instance Morphism2 (FIPIς val lτ dτ ψ) (((ID :.: (,) (Store val lτ dτ ψ)) :.: ListSet) :.: (,) (PIΣ' lτ dτ ψ)) where
  morph2 = Compose . Compose . Compose . ID . mapSnd (map swap) . swap . runFIPIς
instance Morphism2 (((ID :.: (,) (Store val lτ dτ ψ)) :.: ListSet) :.: (,) (PIΣ' lτ dτ ψ)) (FIPIς val lτ dτ ψ) where
  morph2 = FIPIς . swap . mapSnd (map swap) . runID . runCompose . runCompose . runCompose
instance (TimeC lτ, TimeC dτ) => Inject (FIPIς val lτ dτ Ψ) where
  inj = FIPIς . (,initial) . inj . (,initial)
instance Isomorphism2 (FIPIς val lτ dτ ψ) (((ID :.: (,) (Store val lτ dτ ψ)) :.: ListSet) :.: (,) (PIΣ' lτ dτ ψ)) where
newtype FIPI val lτ dτ ψ a = FIPI 
  { runFIPI :: IsoMonadStep (FIPIς val lτ dτ ψ) (((ID :.: (,) (Store val lτ dτ ψ)) :.: ListSet) :.: (,) (PIΣ' lτ dτ ψ))
                 (AddStateT (PIΣ val lτ dτ ψ) (PIΣ' lτ dτ ψ) (ListSetT (StateT (Store val lτ dτ ψ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (PIΣ val lτ dτ ψ), MonadStateI (PIΣ val lτ dτ ψ), MonadState (PIΣ val lτ dτ ψ)
    , MonadStep (FIPIς val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (PIΣ val lτ dτ Ψ) (FIPIς val lτ dτ Ψ) (FIPI val lτ dτ Ψ) where
