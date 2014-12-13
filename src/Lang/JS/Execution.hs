module Lang.JS.Execution where

import FP
import MAAM
import Lang.JS.StateSpace
import Lang.JS.Syntax
import Lang.JS.Semantics
import Lang.JS.Pretty ()

-- The type that is automatically generated as the state space functor for M
type Σ' = (((ID :.: (,) (Store, KStore)) :.: ListSet) :.: (,) (Env, KAddr, Addr, KAddr))

-- A nicer to look at state space functor that is isomorphic to Σ'
newtype Σ a = Σ { unΣ :: (ListSet (a, Env, KAddr, Addr, KAddr), Store, KStore) }
  deriving (PartialOrder, JoinLattice, Pretty)
instance Inject Σ where 
  inj :: a -> Σ a
  inj a = Σ (inj (a, ρ₀, κ₀, τ₀, κτ₀), σ₀, κσ₀)
    where
      𝒮 ρ₀ σ₀ κσ₀ κ₀ τ₀ κτ₀ = initial
instance Morphism2 Σ Σ' where 
  morph2 = Compose . Compose . Compose . ID . ff . unΣ
    where 
      ff (ς, σ, κσ) = ((σ, κσ), map gg ς)
      gg (a, ρ, κ, τ, κτ) = ((ρ, κ, τ, κτ), a)
instance Morphism2 Σ' Σ where 
  morph2 = Σ . ff . runID . runCompose . runCompose . runCompose
    where
      ff ((σ, κσ), ς) = (map gg ς, σ, κσ)
      gg ((ρ, κ, τ, κτ), a) = (a, ρ, κ, τ, κτ)
instance Isomorphism2 Σ Σ'

-- A version of Σ that stores a Set rather than ListSet
newtype Σ𝒫 a = Σ𝒫 { unΣ𝒫 :: (Set (a, Env, KAddr, Addr, KAddr), Store, KStore) }
  deriving (PartialOrder, JoinLattice, Pretty)

instance (Ord a) => Morphism (Σ a) (Σ𝒫 a) where
  morph (Σ (cs, σ, κσ)) = Σ𝒫 (iter insert empty cs, σ, κσ)
instance (Ord a) => Morphism (Σ𝒫 a) (Σ a) where
  morph (Σ𝒫 (cs, σ, κσ)) = Σ (foldr cons nil cs, σ, κσ)
instance (Ord a) => Isomorphism (Σ a) (Σ𝒫 a)

injΣ𝒫 :: forall a. (Ord a) => a -> Σ𝒫 a
injΣ𝒫 a = morph ς
  where
    ς :: Σ a
    ς = inj a

-- The type that is generated for the state cell for M, which is isomorphic to 𝒮
type 𝒮' = ((Env, KAddr, Addr, KAddr), (Store, KStore))
instance Morphism 𝒮 𝒮' where
  morph (𝒮 ρ σ κσ κ τ κτ) = ((ρ, κ, τ, κτ), (σ, κσ))
instance Morphism 𝒮' 𝒮 where
  morph ((ρ, κ, τ, κτ), (σ, κσ)) = 𝒮 ρ σ κσ κ τ κτ
instance Isomorphism 𝒮 ((Env, KAddr, Addr, KAddr), (Store, KStore))

-- A monad that satisfies the Analysis constraint
type M' = IsoMonadStep Σ Σ' 
          (AddStateT 𝒮 (Env, KAddr, Addr, KAddr) 
           (ListSetT 
            (StateT (Store, KStore) 
             ID)))
newtype M a = M { unM :: M' a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE 𝒮, MonadStateI 𝒮, MonadState 𝒮
    , MonadStep Σ
    )
instance Analysis Σ M

instance Initial 𝒮 where
  initial = 𝒮 ρ₀ σ₀ mapEmpty (KAddr 0) (Addr 0) (KAddr 0)
    where
      ρ₀ = fromList [(Name "$global", Addr 0)]
      σ₀ = fromList [(Addr 0, singleton $ ObjA $ Obj [])]

execM :: TExp -> Σ𝒫 TExp
execM = collect (isoto . mstepγ evalM . isofrom) . injΣ𝒫
  where
    evalM :: TExp -> M TExp
    evalM = eval
