module Lang.LamIf.Monads where

import FP
import MAAM
import Lang.LamIf.Semantics
import Lang.LamIf.StateSpace
import Lang.LamIf.Pretty ()

-- Path Sensitive
type PSΣ' val lτ dτ ψ = (ID :.: ListSet) :.: (,) (𝒮 val lτ dτ ψ)

newtype PSΣ val lτ dτ ψ a = PSΣ { runPSΣ :: ListSet (a, 𝒮 val lτ dτ ψ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance Morphism2 (PSΣ val lτ dτ ψ) (PSΣ' val lτ dτ ψ)  where
  morph2 = Compose . Compose . ID . map swap . runPSΣ
instance Morphism2 (PSΣ' val lτ dτ ψ) (PSΣ val lτ dτ ψ) where
  morph2 = PSΣ . map swap . unID . unCompose . unCompose
instance Isomorphism2 (PSΣ val lτ dτ ψ) (PSΣ' val lτ dτ ψ) where
instance (TimeC lτ, TimeC dτ) => Inject (PSΣ val lτ dτ Ψ) where
  inj = PSΣ . inj . (,initial)

newtype PSΣ𝒫 val lτ dτ ψ a = PSΣ𝒫 { runPSΣ𝒫 :: Set (a, 𝒮 val lτ dτ ψ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Morphism (PSΣ val lτ dτ ψ a) (PSΣ𝒫 val lτ dτ ψ a) where
  morph (PSΣ a𝓈s) = PSΣ𝒫 $ toSet $ toList a𝓈s
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Morphism (PSΣ𝒫 val lτ dτ ψ a) (PSΣ val lτ dτ ψ a) where
  morph (PSΣ𝒫 a𝓈s) = PSΣ $ fromList $ toList a𝓈s
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Isomorphism (PSΣ val lτ dτ ψ a) (PSΣ𝒫 val lτ dτ ψ a)

newtype PS val lτ dτ ψ a = FSPS 
  { runPS :: IsoMonadStep (PSΣ val lτ dτ ψ) (PSΣ' val lτ dτ ψ) 
                 (StateT (𝒮 val lτ dτ ψ) (ListSetT ID)) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (𝒮 val lτ dτ ψ), MonadStateI (𝒮 val lτ dτ ψ), MonadState (𝒮 val lτ dτ ψ)
    , MonadStep (PSΣ val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (PS val lτ dτ Ψ)
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Execution (PSΣ val lτ dτ Ψ) (PSΣ𝒫 val lτ dτ Ψ) (PS val lτ dτ Ψ)

-- Path Insensitive
data PI𝒮 lτ dτ ψ = PI𝒮
  { pilτ :: lτ ψ
  , pidτ :: dτ ψ
  , piρ :: Env lτ dτ ψ
  } deriving (Eq, Ord)
makePrettyUnion ''PI𝒮
instance (Initial (lτ ψ), Initial (dτ ψ)) => Initial (PI𝒮 lτ dτ ψ) where
  initial = PI𝒮 initial initial initial
instance Morphism (𝒮 val lτ dτ ψ) (PI𝒮 lτ dτ ψ, Store val lτ dτ ψ) where
  morph (𝒮 lτ dτ ρ σ) = (PI𝒮 lτ dτ ρ, σ)
instance Morphism (PI𝒮 lτ dτ ψ, Store val lτ dτ ψ) (𝒮 val lτ dτ ψ) where
  morph (PI𝒮 lτ dτ ρ, σ) = 𝒮 lτ dτ ρ σ
instance Isomorphism (𝒮 val lτ dτ ψ) (PI𝒮 lτ dτ ψ, Store val lτ dτ ψ)

-- Flow Sensitive Path Insensitive
type FSΣ' val lτ dτ ψ = (ListSet :.: ID :.: (,) (Store val lτ dτ ψ)) :.: (,) (PI𝒮 lτ dτ ψ)

newtype FSΣ val lτ dτ ψ a = FSΣ { runFSΣ :: ListSet (a, 𝒮 val lτ dτ ψ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance Morphism2 (FSΣ val lτ dτ ψ) (FSΣ' val lτ dτ ψ) where
  morph2 = Compose . Compose . map (Compose . ID . (\ (a, 𝒮 lτ dτ ρ σ) -> (σ, (PI𝒮 lτ dτ ρ, a)))) . runFSΣ
instance Morphism2 (FSΣ' val lτ dτ ψ) (FSΣ val lτ dτ ψ) where
  morph2 = FSΣ . map ((\ (σ, (PI𝒮 lτ dτ ρ, a)) -> (a, 𝒮 lτ dτ ρ σ)) . unID . unCompose) . unCompose . unCompose
instance Isomorphism2 (FSΣ val lτ dτ ψ) (FSΣ' val lτ dτ ψ) where
instance (TimeC lτ, TimeC dτ) => Inject (FSΣ val lτ dτ Ψ) where
  inj = FSΣ . inj . (,initial)

newtype FSΣ𝒫 val lτ dτ ψ a = FSΣ𝒫 { runFSΣ𝒫 :: Set (a, 𝒮 val lτ dτ ψ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Morphism (FSΣ val lτ dτ ψ a) (FSΣ𝒫 val lτ dτ ψ a) where
  morph (FSΣ a𝓈s) = FSΣ𝒫 $ toSet $ toList a𝓈s
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Morphism (FSΣ𝒫 val lτ dτ ψ a) (FSΣ val lτ dτ ψ a) where
  morph (FSΣ𝒫 a𝓈s) = FSΣ $ fromList $ toList a𝓈s
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Isomorphism (FSΣ val lτ dτ ψ a) (FSΣ𝒫 val lτ dτ ψ a)

newtype FS val lτ dτ ψ a = FS 
  { runFS :: IsoMonadStep (FSΣ val lτ dτ ψ) (FSΣ' val lτ dτ ψ)
                 (AddStateT (𝒮 val lτ dτ ψ) (PI𝒮 lτ dτ ψ) (ListSetT (StateT (Store val lτ dτ ψ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (𝒮 val lτ dτ ψ), MonadStateI (𝒮 val lτ dτ ψ), MonadState (𝒮 val lτ dτ ψ)
    , MonadStep (FSΣ val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (FS val lτ dτ Ψ)
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Execution (FSΣ val lτ dτ Ψ) (FSΣ𝒫 val lτ dτ Ψ) (FS val lτ dτ Ψ)

-- Flow Insensitive Path Insensitive
type FIΣ' val lτ dτ ψ = ((ID :.: (,) (Store val lτ dτ ψ)) :.: ListSet) :.: (,) (PI𝒮 lτ dτ ψ)

newtype FIΣ val lτ dτ ψ a = FIΣ { runFIΣ :: (ListSet (a, PI𝒮 lτ dτ ψ), Store val lτ dτ ψ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance Morphism2 (FIΣ val lτ dτ ψ) (FIΣ' val lτ dτ ψ) where
  morph2 = Compose . Compose . Compose . ID . mapSnd (map swap) . swap . runFIΣ
instance Morphism2 (FIΣ' val lτ dτ ψ) (FIΣ val lτ dτ ψ) where
  morph2 = FIΣ . swap . mapSnd (map swap) . unID . unCompose . unCompose . unCompose
instance Isomorphism2 (FIΣ val lτ dτ ψ) (FIΣ' val lτ dτ ψ) where

newtype FIΣ𝒫 val lτ dτ ψ a = FIΣ𝒫 { runFIΣ𝒫 :: (Set (a, PI𝒮 lτ dτ ψ), Store val lτ dτ ψ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Morphism (FIΣ val lτ dτ ψ a) (FIΣ𝒫 val lτ dτ ψ a) where
  morph (FIΣ (a𝓈s, σ)) = FIΣ𝒫 (toSet $ toList a𝓈s, σ)
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Morphism (FIΣ𝒫 val lτ dτ ψ a) (FIΣ val lτ dτ ψ a) where
  morph (FIΣ𝒫 (a𝓈s, σ)) = FIΣ (fromList $ toList a𝓈s, σ)
instance (Ord (val lτ dτ ψ), Ord (lτ ψ), Ord (dτ ψ), Ord a) => Isomorphism (FIΣ val lτ dτ ψ a) (FIΣ𝒫 val lτ dτ ψ a)

instance (TimeC lτ, TimeC dτ) => Inject (FIΣ val lτ dτ Ψ) where
  inj = FIΣ . (,initial) . inj . (,initial)

newtype FI val lτ dτ ψ a = FIPI 
  { runFI :: IsoMonadStep (FIΣ val lτ dτ ψ) (FIΣ' val lτ dτ ψ)
                 (AddStateT (𝒮 val lτ dτ ψ) (PI𝒮 lτ dτ ψ) (ListSetT (StateT (Store val lτ dτ ψ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (𝒮 val lτ dτ ψ), MonadStateI (𝒮 val lτ dτ ψ), MonadState (𝒮 val lτ dτ ψ)
    , MonadStep (FIΣ val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (FI val lτ dτ Ψ)
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Execution (FIΣ val lτ dτ Ψ) (FIΣ𝒫 val lτ dτ Ψ) (FI val lτ dτ Ψ)
