module Lang.Hask.Monads where

import FP
import MAAM hiding (Time(..))
import Lang.Hask.Semantics
import Lang.Hask.Execution

type PSΣ' ν lτ dτ = (ID :.: ListSetWithTop) :.: (,) (𝒮 ν lτ dτ)

newtype PSΣ ν lτ dτ a = PSΣ { runPSΣ :: ListSetWithTop (a, 𝒮 ν lτ dτ) } deriving (PartialOrder, Bot, Join, JoinLattice)
instance Morphism2 (PSΣ ν lτ dτ) (PSΣ' ν lτ dτ)  where morph2 = Compose . Compose . ID . map swap . runPSΣ
instance Morphism2 (PSΣ' ν lτ dτ) (PSΣ ν lτ dτ) where morph2 = PSΣ . map swap . unID . unCompose . unCompose
instance (TimeC lτ dτ) => Inject (PSΣ ν lτ dτ) where inj = PSΣ . inj . (,bot)
instance Isomorphism2 (PSΣ ν lτ dτ) (PSΣ' ν lτ dτ)

newtype PSΣ𝒫 ν lτ dτ a = PSΣ𝒫 { runPSΣ𝒫 :: SetWithTop (a, 𝒮 ν lτ dτ) }
  deriving (PartialOrder, Bot, Join, JoinLattice)
instance (Ord (ν lτ dτ), Ord lτ, Ord dτ, Ord a) => Morphism (PSΣ ν lτ dτ a) (PSΣ𝒫 ν lτ dτ a) where
  morph (PSΣ a𝓈s) = PSΣ𝒫 $ setFromListWithTop a𝓈s
instance (Ord (ν lτ dτ), Ord lτ, Ord dτ, Ord a) => Morphism (PSΣ𝒫 ν lτ dτ a) (PSΣ ν lτ dτ a) where
  morph (PSΣ𝒫 a𝓈s) = PSΣ $ listFromSetWithTop a𝓈s
instance (Ord (ν lτ dτ), Ord lτ, Ord dτ, Ord a) => Isomorphism (PSΣ ν lτ dτ a) (PSΣ𝒫 ν lτ dτ a)

newtype PS ν lτ dτ a = FSPS 
  { runPS :: IsoMonadStep (PSΣ ν lτ dτ) (PSΣ' ν lτ dτ) 
                 (StateT (𝒮 ν lτ dτ) (ListSetWithTopT ID)) a 
  } deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadBot, MonadPlus, MonadTop
    , MonadState (𝒮 ν lτ dτ)
    , MonadStep (PSΣ ν lτ dτ)
    )
instance (TimeC lτ dτ, ValC ν lτ dτ) => Analysis ν lτ dτ (PS ν lτ dτ)
instance (TimeC lτ dτ, Ord (ν lτ dτ)) => Execution (PSΣ ν lτ dτ) (PS ν lτ dτ)
