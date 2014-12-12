module Lang.JS.Execution where

import FP
import MAAM
import Lang.JS.JS
import Lang.JS.Syntax

-- The type that is automatically generated as the state space functor for M
type MΣ' = (((ID :.: (,) (Store, KStore)) :.: ListSet) :.: (,) (Env, KAddr, Addr, KAddr))

-- data Σ = Σ
--   { env :: Env
--   , store :: Store
--   , kstore :: KStore
--   , kon :: KAddr
--   , nextAddr :: Addr
--   , nextKAddr :: KAddr
--   } deriving (Eq, Ord)
-- A nicer to look at state space functor that is isomorphic to MΣ'
newtype MΣ a = MΣ { unMΣ :: (ListSet (a, Env, KAddr, Addr, KAddr), Store, KStore) }
  deriving (PartialOrder, JoinLattice)
instance Inject MΣ where 
  inj :: a -> MΣ a
  inj a = MΣ (inj (a, ρ₀, κ₀, τ₀, κτ₀), σ₀, κσ₀)
    where
      Σ ρ₀ σ₀ κσ₀ κ₀ τ₀ κτ₀ = initial
instance Morphism2 MΣ MΣ' where 
  morph2 = Compose . Compose . Compose . ID . ff . unMΣ
    where 
      ff (ς, σ, κσ) = ((σ, κσ), map gg ς)
      gg (a, ρ, κ, τ, κτ) = ((ρ, κ, τ, κτ), a)
instance Morphism2 MΣ' MΣ where 
  morph2 = MΣ . ff . runID . runCompose . runCompose . runCompose
    where
      ff ((σ, κσ), ς) = (map gg ς, σ, κσ)
      gg ((ρ, κ, τ, κτ), a) = (a, ρ, κ, τ, κτ)
instance Isomorphism2 MΣ MΣ'

instance Morphism Σ ((Env, KAddr, Addr, KAddr), (Store, KStore)) where
  morph (Σ ρ σ κσ κ τ κτ) = ((ρ, κ, τ, κτ), (σ, κσ))
instance Morphism ((Env, KAddr, Addr, KAddr), (Store, KStore)) Σ where
  morph ((ρ, κ, τ, κτ), (σ, κσ)) = Σ ρ σ κσ κ τ κτ
instance Isomorphism Σ ((Env, KAddr, Addr, KAddr), (Store, KStore))

-- A monad that satisfies the Analysis constraint
newtype M a = M { unM :: IsoMonadStep MΣ MΣ' (AddStateT Σ (Env, KAddr, Addr, KAddr) (ListSetT (StateT (Store, KStore) ID))) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE Σ, MonadStateI Σ, MonadState Σ
    , MonadStep MΣ
    )
instance Analysis MΣ M

instance Initial Σ where
  initial = Σ ρ₀ σ₀ mapEmpty (KAddr 0) (Addr 0) (KAddr 0)
    where
      ρ₀ = fromList [(Name "$global", Addr 0)]
      σ₀ = fromList [(Addr 0, singleton $ ObjA $ Obj [])]

execM :: TExp -> (Set (TExp, Env, KAddr, Addr, KAddr), Store, KStore)
execM = (\ (ς, σ, κσ) -> (toSet $ toList ς, σ, κσ)) . unMΣ . collect (mstepγ evalM) . inj
  where
    evalM :: TExp -> M TExp
    evalM = eval
