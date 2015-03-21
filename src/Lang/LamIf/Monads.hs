module Lang.LamIf.Monads where

import FP
import MAAM
import Lang.LamIf.Semantics
import Lang.LamIf.StateSpace
import Lang.LamIf.Pretty ()

-- Path Sensitive
type PSΣ' val lτ dτ = (ID :.: ListSet) :.: (,) (𝒮 val lτ dτ)
newtype PSΣ val lτ dτ a = PSΣ { unPSΣ :: ListSet (a, 𝒮 val lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance Morphism2 (PSΣ val lτ dτ) (PSΣ' val lτ dτ)  where
  morph2 = Compose . Compose . ID . map swap . unPSΣ
instance Morphism2 (PSΣ' val lτ dτ) (PSΣ val lτ dτ) where
  morph2 = PSΣ . map swap . unID . unCompose . unCompose
instance Isomorphism2 (PSΣ val lτ dτ) (PSΣ' val lτ dτ) where
instance (TimeC lτ, TimeC dτ) => Inject (PSΣ val lτ dτ) where
  inj = PSΣ . inj . (,bot)

newtype PSΣ𝒫 val lτ dτ a = PSΣ𝒫 { unPSΣ𝒫 :: Set (a, 𝒮 val lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty, Difference)
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Morphism (PSΣ val lτ dτ a) (PSΣ𝒫 val lτ dτ a) where
  morph (PSΣ a𝓈s) = PSΣ𝒫 $ toSet $ toList a𝓈s
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Morphism (PSΣ𝒫 val lτ dτ a) (PSΣ val lτ dτ a) where
  morph (PSΣ𝒫 a𝓈s) = PSΣ $ fromList $ toList a𝓈s
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Isomorphism (PSΣ val lτ dτ a) (PSΣ𝒫 val lτ dτ a)

newtype PS val lτ dτ a = FSPS 
  { unPS :: IsoMonadStep (PSΣ val lτ dτ) (PSΣ' val lτ dτ) 
                 (StateT (𝒮 val lτ dτ) (ListSetT ID)) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadBot, MonadPlus
    , MonadState (𝒮 val lτ dτ)
    , MonadStep (PSΣ val lτ dτ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (PS val lτ dτ)
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Execution (PSΣ val lτ dτ) (PSΣ𝒫 val lτ dτ) (PS val lτ dτ)

-- Flow Sensitive Path Insensitive
type FSΣ' val lτ dτ = (ID :.: ListSet) :.: (,) (𝒮 val lτ dτ)

newtype FSΣ val lτ dτ a = FSΣ { unFSΣ :: ListSet (a, 𝒮 val lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance Morphism2 (FSΣ val lτ dτ) (FSΣ' val lτ dτ)  where
  morph2 = Compose . Compose . ID . map swap . unFSΣ
instance Morphism2 (FSΣ' val lτ dτ) (FSΣ val lτ dτ) where
  morph2 = FSΣ . map swap . unID . unCompose . unCompose
instance Isomorphism2 (FSΣ val lτ dτ) (FSΣ' val lτ dτ) where
instance (TimeC lτ, TimeC dτ) => Inject (FSΣ val lτ dτ) where
  inj = FSΣ . inj . (,bot)

newtype FSΣ𝒫 val lτ dτ a = FSΣ𝒫 { unFSΣ𝒫 :: Map a (Set (𝒮Cxt lτ dτ), Store val lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty, Difference)
instance (Ord val, Join val, Ord lτ, Ord dτ, Ord a) => Morphism (FSΣ val lτ dτ a) (FSΣ𝒫 val lτ dτ a) where
  morph = FSΣ𝒫 . toMapJoin . map (mapSnd $ \ (𝒮 cxt σ) -> (single cxt, σ)) . toList . unFSΣ
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Morphism (FSΣ𝒫 val lτ dτ a) (FSΣ val lτ dτ a) where
  morph = FSΣ . fromList . toList . joins . map (\ (a, (cxts, σ)) -> setMapOn cxts $ \ cxt -> (a, 𝒮 cxt σ)) . toList . unFSΣ𝒫
instance (Ord val, Join val, Ord lτ, Ord dτ, Ord a) => Isomorphism (FSΣ val lτ dτ a) (FSΣ𝒫 val lτ dτ a)

newtype FS val lτ dτ a = FS 
  { unFS :: IsoMonadStep (FSΣ val lτ dτ) (FSΣ' val lτ dτ) 
                 (StateT (𝒮 val lτ dτ) (ListSetT ID)) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadBot, MonadPlus
    , MonadState (𝒮 val lτ dτ)
    , MonadStep (FSΣ val lτ dτ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (FS val lτ dτ)
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Execution (FSΣ val lτ dτ) (FSΣ𝒫 val lτ dτ) (FS val lτ dτ)

-- Path Insensitive
instance Morphism (𝒮 val lτ dτ) (𝒮Cxt lτ dτ, Store val lτ dτ) where
  morph (𝒮 cxt σ) = (cxt, σ)
instance Morphism (𝒮Cxt lτ dτ, Store val lτ dτ) (𝒮 val lτ dτ) where
  morph (cxt, σ) = 𝒮 cxt σ
instance Isomorphism (𝒮 val lτ dτ) (𝒮Cxt lτ dτ, Store val lτ dτ)

-- Flow Insensitive Path Insensitive
type FIΣ' val lτ dτ = ((ID :.: (,) (Store val lτ dτ)) :.: ListSet) :.: (,) (𝒮Cxt lτ dτ)

newtype FIΣ val lτ dτ a = FIΣ { unFIΣ :: (ListSet (a, 𝒮Cxt lτ dτ), Store val lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Pretty)
instance Morphism2 (FIΣ val lτ dτ) (FIΣ' val lτ dτ) where
  morph2 = Compose . Compose . Compose . ID . mapSnd (map swap) . swap . unFIΣ
instance Morphism2 (FIΣ' val lτ dτ) (FIΣ val lτ dτ) where
  morph2 = FIΣ . swap . mapSnd (map swap) . unID . unCompose . unCompose . unCompose
instance Isomorphism2 (FIΣ val lτ dτ) (FIΣ' val lτ dτ) where

newtype FIΣ𝒫 val lτ dτ a = FIΣ𝒫 { unFIΣ𝒫 :: (Set (a, 𝒮Cxt lτ dτ), Store val lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice, Difference, Pretty)
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Morphism (FIΣ val lτ dτ a) (FIΣ𝒫 val lτ dτ a) where
  morph (FIΣ (a𝓈s, σ)) = FIΣ𝒫 (toSet $ toList a𝓈s, σ)
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Morphism (FIΣ𝒫 val lτ dτ a) (FIΣ val lτ dτ a) where
  morph (FIΣ𝒫 (a𝓈s, σ)) = FIΣ (fromList $ toList a𝓈s, σ)
instance (Ord val, Ord lτ, Ord dτ, Ord a) => Isomorphism (FIΣ val lτ dτ a) (FIΣ𝒫 val lτ dτ a)

instance (TimeC lτ, TimeC dτ) => Inject (FIΣ val lτ dτ) where
  inj = FIΣ . (,bot) . inj . (,bot)

newtype FI val lτ dτ a = FIPI 
  { unFI :: IsoMonadStep (FIΣ val lτ dτ) (FIΣ' val lτ dτ)
                 (AddStateT (𝒮 val lτ dτ) (𝒮Cxt lτ dτ) (ListSetT (StateT (Store val lτ dτ) ID))) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadBot, MonadPlus
    , MonadState (𝒮 val lτ dτ)
    , MonadStep (FIΣ val lτ dτ)
    )
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Analysis val lτ dτ (FI val lτ dτ)
instance (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Execution (FIΣ val lτ dτ) (FIΣ𝒫 val lτ dτ) (FI val lτ dτ)
