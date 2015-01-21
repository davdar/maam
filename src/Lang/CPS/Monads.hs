module Lang.CPS.Monads where

import FP
import MAAM
import Lang.CPS.Semantics
import Lang.CPS.StateSpace
import Lang.CPS.Pretty ()

-- Path Sensitive
type PSΣ' val lτ dτ ψ = (ID :.: ListSet) :.: (,) (𝒮 val lτ dτ ψ)
newtype PSΣ val lτ dτ ψ a = PSΣ { runPSΣ :: ListSet (a, 𝒮 val lτ dτ ψ) }
  deriving (PartialOrder, JoinLattice, Pretty)
instance Morphism2 (PSΣ val lτ dτ ψ) (PSΣ' val lτ dτ ψ)  where
  morph2 = Compose . Compose . ID . map swap . runPSΣ
instance Morphism2 (PSΣ' val lτ dτ ψ) (PSΣ val lτ dτ ψ) where
  morph2 = PSΣ . map swap . runID . runCompose . runCompose
instance Isomorphism2 (PSΣ val lτ dτ ψ) (PSΣ' val lτ dτ ψ) where
instance (TimeC lτ, TimeC dτ) => Inject (PSΣ val lτ dτ Ψ) where
  inj = PSΣ . inj . (,initial)

newtype PS val lτ dτ ψ a = FSPS 
  { runPS :: IsoMonadStep (PSΣ val lτ dτ ψ) (PSΣ' val lτ dτ ψ) 
                 (StateT (𝒮 val lτ dτ ψ) (ListSetT ID)) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (𝒮 val lτ dτ ψ), MonadStateI (𝒮 val lτ dτ ψ), MonadState (𝒮 val lτ dτ ψ)
    , MonadStep (PSΣ val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (PSΣ val lτ dτ Ψ) (PS val lτ dτ Ψ) where

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
  deriving (PartialOrder, JoinLattice, Pretty)
instance Morphism2 (FSΣ val lτ dτ ψ) (FSΣ' val lτ dτ ψ) where
  morph2 = Compose . Compose . map (Compose . ID . (\ (a, 𝒮 lτ dτ ρ σ) -> (σ, (PI𝒮 lτ dτ ρ, a)))) . runFSΣ
instance Morphism2 (FSΣ' val lτ dτ ψ) (FSΣ val lτ dτ ψ) where
  morph2 = FSΣ . map ((\ (σ, (PI𝒮 lτ dτ ρ, a)) -> (a, 𝒮 lτ dτ ρ σ)) . runID . runCompose) . runCompose . runCompose
instance Isomorphism2 (FSΣ val lτ dτ ψ) (FSΣ' val lτ dτ ψ) where
instance (TimeC lτ, TimeC dτ) => Inject (FSΣ val lτ dτ Ψ) where
  inj = FSΣ . inj . (,initial)
newtype FS val lτ dτ ψ a = FS 
  { runFS :: IsoMonadStep (FSΣ val lτ dτ ψ) (FSΣ' val lτ dτ ψ)
                 (AddStateT (𝒮 val lτ dτ ψ) (PI𝒮 lτ dτ ψ) (ListSetT (StateT (Store val lτ dτ ψ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (𝒮 val lτ dτ ψ), MonadStateI (𝒮 val lτ dτ ψ), MonadState (𝒮 val lτ dτ ψ)
    , MonadStep (FSΣ val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (FSΣ val lτ dτ Ψ) (FS val lτ dτ Ψ) where

-- Flow Insensitive Path Insensitive
type FIΣ' val lτ dτ ψ = ((ID :.: (,) (Store val lτ dτ ψ)) :.: ListSet) :.: (,) (PI𝒮 lτ dτ ψ)
newtype FIΣ val lτ dτ ψ a = FIΣ { runFIΣ :: (ListSet (a, PI𝒮 lτ dτ ψ), Store val lτ dτ ψ) }
  deriving (PartialOrder, JoinLattice, Pretty)
instance Morphism2 (FIΣ val lτ dτ ψ) (FIΣ' val lτ dτ ψ) where
  morph2 = Compose . Compose . Compose . ID . mapSnd (map swap) . swap . runFIΣ
instance Morphism2 (FIΣ' val lτ dτ ψ) (FIΣ val lτ dτ ψ) where
  morph2 = FIΣ . swap . mapSnd (map swap) . runID . runCompose . runCompose . runCompose
instance (TimeC lτ, TimeC dτ) => Inject (FIΣ val lτ dτ Ψ) where
  inj = FIΣ . (,initial) . inj . (,initial)
instance Isomorphism2 (FIΣ val lτ dτ ψ) (FIΣ' val lτ dτ ψ) where
newtype FI val lτ dτ ψ a = FIPI 
  { runFI :: IsoMonadStep (FIΣ val lτ dτ ψ) (FIΣ' val lτ dτ ψ)
                 (AddStateT (𝒮 val lτ dτ ψ) (PI𝒮 lτ dτ ψ) (ListSetT (StateT (Store val lτ dτ ψ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE (𝒮 val lτ dτ ψ), MonadStateI (𝒮 val lτ dτ ψ), MonadState (𝒮 val lτ dτ ψ)
    , MonadStep (FIΣ val lτ dτ ψ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (FIΣ val lτ dτ Ψ) (FI val lτ dτ Ψ) where
