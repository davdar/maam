module Lang.LamIf.Monads where

import FP
import MAAM
import Lang.LamIf.Stamp
import Lang.LamIf.Semantics
import Lang.LamIf.Values
import Lang.LamIf.Domains

-- # Common Injection

newtype InjectLamIf val a = InjectLamIf { runInjectLamIf ∷ (a,LamIfState val) }

isoInjectLamIf ∷ InjectLamIf val a ⇄ (a,LamIfState val)
isoInjectLamIf = Iso runInjectLamIf InjectLamIf

-- # Path Sensitive

-- Transition System

newtype PathSensitiveΣᵇ val a = PathSensitiveΣᵇ { runPathSensitiveΣᵇ ∷ PolyStateΠ (LamIfState val) (NondetJoinΠ ID) a }

isoPathSensitiveΣᵇ ∷ PathSensitiveΣᵇ val a ⇄ PolyStateΠ (LamIfState val) (NondetJoinΠ ID) a
isoPathSensitiveΣᵇ = Iso runPathSensitiveΣᵇ PathSensitiveΣᵇ

isoPathSensitiveΣᵇ2 ∷ PathSensitiveΣᵇ val ↝⇄ PolyStateΠ (LamIfState val) (NondetJoinΠ ID)
isoPathSensitiveΣᵇ2 = iso2FromIso isoPathSensitiveΣᵇ

instance Inject (InjectLamIf val) (PathSensitiveΣᵇ val) where
  inject = isoInject (iso2FromIso $ sym $ sym isoInjectLamIf ⌾ isoID ⌾ isoStateI) isoPathSensitiveΣᵇ2

newtype PathSensitiveΣ val a = PathSensitiveΣ { runPathSensitiveΣ ∷ 𝒫 (a,LamIfState val) }
  deriving (POrd,Bot,Join,JoinLattice,Difference,Pretty)

isoPathSensitiveΣ ∷ (Ord val,Ord a) ⇒ PathSensitiveΣ val a ⇄ PathSensitiveΣᵇ val a
isoPathSensitiveΣ = Iso 
  (PathSensitiveΣᵇ  ∘ PolyStateΠ ∘ NondetJoinΠ ∘ ID ∘ lazySet ∘ runPathSensitiveΣ) 
  (PathSensitiveΣ ∘ set ∘ runID ∘ runNondetJoinΠ ∘ runPolyStateΠ  ∘ runPathSensitiveΣᵇ)

-- Monad

newtype PathSensitiveM val a = PathSensitiveM { runPathSensitiveM ∷ PolyStateT (LamIfState val) (NondetJoinT ID) a }
  deriving 
  (Functor,Monad,MonadBot,MonadJoin,MonadJoinLattice,MonadState (LamIfState val))

isoPathSensitiveM ∷ PathSensitiveM val a ⇄ PolyStateT (LamIfState val) (NondetJoinT ID) a
isoPathSensitiveM = Iso runPathSensitiveM PathSensitiveM

isoPathSensitiveM2 ∷ PathSensitiveM val ↝⇄ PolyStateT (LamIfState val) (NondetJoinT ID)
isoPathSensitiveM2 = iso2FromIso isoPathSensitiveM

instance GaloisTransformer (PathSensitiveΣᵇ val) (PathSensitiveM val) where
  αGT = isoαGT isoPathSensitiveΣᵇ2 isoPathSensitiveM2
  γGT = isoγGT isoPathSensitiveΣᵇ2 isoPathSensitiveM2

-- Execution

instance (POrd val,JoinLattice val,Val val) ⇒ 
  MonadLamIf val (PathSensitiveM val)

instance (Ord val,POrd val,JoinLattice val,Val val) ⇒ 
  ExecutionLamIf val 
  (InjectLamIf val)
  (PathSensitiveΣᵇ val)
  (PathSensitiveM val)

-- # Path Insensitive

data LamIfContext val = LamIfContext
  { ctxEnv ∷ Env 
  , ctxΚAddr ∷ Maybe ExpAddr 
  , ctxTime ∷ Time 
  } deriving (Eq,Ord)
makePrettyRecord ''LamIfContext

data LamIfStores val = LamIfStores
  { storesStore ∷ Store val
  , storesΚStore ∷ KStore val
  } deriving (Eq,Ord)
makePrettyRecord ''LamIfStores

instance (POrd val) ⇒ POrd (LamIfStores val) where
  (⊑⊒) = poCompareFromLte $ \ (LamIfStores σ₁ κσ₁) (LamIfStores σ₂ κσ₂) → meets [σ₁ ⊑ σ₂,κσ₁ ⊑ κσ₂]
instance Bot (LamIfStores val) where
  bot = LamIfStores bot bot
instance (Join val) ⇒ Join (LamIfStores val) where
  LamIfStores σ₁ κσ₁ ⊔ LamIfStores σ₂ κσ₂ = LamIfStores (σ₁ ⊔ σ₂) (κσ₁ ⊔ κσ₂)
instance (Join val) ⇒ JoinLattice (LamIfStores val)
instance (Difference val) ⇒ Difference (LamIfStores val) where
  LamIfStores σ₁ κσ₁ ⊟ LamIfStores σ₂ κσ₂ = LamIfStores (σ₁ ⊟ σ₂) (κσ₁ ⊟ κσ₂)

splitLamIfState ∷ LamIfState val → (LamIfContext val,LamIfStores val)
splitLamIfState (LamIfState ρ κl τ σ κσ) = (LamIfContext ρ κl τ,LamIfStores σ κσ)

combineLamIfState ∷ (LamIfContext val,LamIfStores val) → LamIfState val
combineLamIfState (LamIfContext ρ κl τ,LamIfStores σ κσ) = LamIfState ρ κl τ σ κσ

isoSplitLamIfState ∷ LamIfState val ⇄ (LamIfContext val,LamIfStores val)
isoSplitLamIfState = Iso splitLamIfState combineLamIfState

isoCombineLamIfState ∷ (a,LamIfState val) ⇄ ((a,LamIfContext val),LamIfStores val)
isoCombineLamIfState = Iso 
  (\ (x,splitLamIfState → (ctx,stores)) → ((x,ctx),stores))
  (\ ((x,ctx),stores) → (x,combineLamIfState (ctx,stores)))

-- ## Flow Sensitive

-- Transition System

newtype FlowSensitiveΣᵇ val a = FlowSensitiveΣᵇ 
  { runFlowSensitiveΣᵇ ∷ 
      PolyStateΠ (LamIfContext val) 
      (FlowJoinΠ (LamIfStores val)
      ID) a
  }

isoFlowSensitiveΣᵇ ∷ FlowSensitiveΣᵇ val a ⇄ PolyStateΠ (LamIfContext val) (FlowJoinΠ (LamIfStores val) ID) a
isoFlowSensitiveΣᵇ = Iso runFlowSensitiveΣᵇ FlowSensitiveΣᵇ

isoFlowSensitiveΣ2ᵇ ∷ FlowSensitiveΣᵇ val ↝⇄ PolyStateΠ (LamIfContext val) (FlowJoinΠ (LamIfStores val) ID)
isoFlowSensitiveΣ2ᵇ = iso2FromIso isoFlowSensitiveΣᵇ

instance Inject (InjectLamIf val) (FlowSensitiveΣᵇ val) where
  inject = isoInject 
    (iso2FromIso $ sym (sym isoCombineLamIfState ⌾ isoID ⌾ isoStateI ⌾ isoStateI) ⌾ isoInjectLamIf)
    isoFlowSensitiveΣ2ᵇ

newtype FlowSensitiveΣ val a = FlowSensitiveΣ { runFlowSensitiveΣ ∷ (a,LamIfContext val) ⇰ LamIfStores val }
  deriving (POrd,Bot,Join,JoinLattice,Difference,Pretty)

isoFlowSensitiveΣ ∷ (Ord a,Join val) ⇒ FlowSensitiveΣ val a ⇄ FlowSensitiveΣᵇ val a
isoFlowSensitiveΣ = Iso 
  (FlowSensitiveΣᵇ ∘ PolyStateΠ ∘ FlowJoinΠ ∘ ID ∘ lazyDictJoin ∘ runFlowSensitiveΣ) 
  (FlowSensitiveΣ ∘ dictJoin ∘ runID ∘ runFlowJoinΠ ∘ runPolyStateΠ ∘ runFlowSensitiveΣᵇ)

-- Monad

newtype FlowSensitiveM val a = FlowSensitiveM
  { runFlowSensitiveM ∷
      PolyStateT (LamIfContext val)
      (FlowJoinT (LamIfStores val)
      ID) a
  }
  deriving (Functor,Monad,MonadBot,MonadJoin,MonadJoinLattice)

isoFlowSensitiveM ∷ FlowSensitiveM val a ⇄ PolyStateT (LamIfContext val) (FlowJoinT (LamIfStores val) ID) a
isoFlowSensitiveM = Iso runFlowSensitiveM FlowSensitiveM

isoFlowSensitiveM2 ∷ FlowSensitiveM val ↝⇄ PolyStateT (LamIfContext val) (FlowJoinT (LamIfStores val) ID)
isoFlowSensitiveM2 = iso2FromIso isoFlowSensitiveM

instance (Join val) ⇒ MonadState (LamIfState val) (FlowSensitiveM val) where
  stateE ∷ StateT (LamIfState val) (FlowSensitiveM val) ↝ FlowSensitiveM val
  stateE = 
    FlowSensitiveM
    ∘ PolyStateT
    ∘ fmap stateE
    ∘ stateE
    ∘ fmap stateCommute
    ∘ splitState
    ∘ mapState isoSplitLamIfState
    ∘ fmap (runPolyStateT ∘ runFlowSensitiveM)
  stateI ∷ FlowSensitiveM val ↝ StateT (LamIfState val) (FlowSensitiveM val)
  stateI =
    fmap (FlowSensitiveM ∘ PolyStateT)
    ∘ mapState (sym isoSplitLamIfState)
    ∘ mergeState
    ∘ fmap stateCommute
    ∘ stateI
    ∘ fmap stateI
    ∘ runPolyStateT
    ∘ runFlowSensitiveM

instance (Join val) ⇒ GaloisTransformer (FlowSensitiveΣᵇ val) (FlowSensitiveM val) where
  αGT = isoαGT isoFlowSensitiveΣ2ᵇ isoFlowSensitiveM2
  γGT = isoγGT isoFlowSensitiveΣ2ᵇ isoFlowSensitiveM2

instance (POrd val,JoinLattice val,Val val) ⇒ 
  MonadLamIf val (FlowSensitiveM val)

instance (Ord val,POrd val,JoinLattice val,Difference val,Val val,Pretty val) ⇒ 
  ExecutionLamIf val 
  (InjectLamIf val)
  (FlowSensitiveΣᵇ val)
  (FlowSensitiveM val)

-- ## Flow Insensitive

-- Transition System

newtype FlowInsensitiveΣᵇ val a = FlowInsensitiveΣᵇ 
  { runFlowInsensitiveΣᵇ ∷ 
      PolyStateΠ (LamIfContext val) 
      (NondetJoinΠ
      (StateΠ (LamIfStores val)
      ID)) a
  }

isoFlowInsensitiveΣᵇ 
  ∷ FlowInsensitiveΣᵇ val a 
  ⇄ PolyStateΠ (LamIfContext val) (NondetJoinΠ (StateΠ (LamIfStores val) ID)) a
isoFlowInsensitiveΣᵇ = Iso runFlowInsensitiveΣᵇ FlowInsensitiveΣᵇ

isoFlowInsensitiveΣᵇ2 
   ∷ FlowInsensitiveΣᵇ val 
  ↝⇄ PolyStateΠ (LamIfContext val) (NondetJoinΠ (StateΠ (LamIfStores val) ID))
isoFlowInsensitiveΣᵇ2 = iso2FromIso isoFlowInsensitiveΣᵇ

instance Inject (InjectLamIf val) (FlowInsensitiveΣᵇ val) where
  inject = isoInject 
    (iso2FromIso $ sym (sym isoCombineLamIfState ⌾ isoID ⌾ isoStateI ⌾ isoStateI) ⌾ isoInjectLamIf)
    isoFlowInsensitiveΣᵇ2

newtype FlowInsensitiveΣ val a = FlowInsensitiveΣ { runFlowInsensitiveΣ ∷ (𝒫(a,LamIfContext val),LamIfStores val) }
  deriving (POrd,Bot,Join,JoinLattice,Difference,Pretty)

isoFlowInsensitiveΣ ∷ (Ord a) ⇒ FlowInsensitiveΣ val a ⇄ FlowInsensitiveΣᵇ val a
isoFlowInsensitiveΣ = Iso
  (FlowInsensitiveΣᵇ ∘ PolyStateΠ ∘ NondetJoinΠ ∘ StateΠ ∘ ID ∘ mapFst lazySet ∘ runFlowInsensitiveΣ)
  (FlowInsensitiveΣ ∘ mapFst set ∘ runID ∘ runStateΠ ∘ runNondetJoinΠ ∘ runPolyStateΠ ∘ runFlowInsensitiveΣᵇ)

-- Monad

newtype FlowInsensitiveM val a = FlowInsensitiveM
  { runFlowInsensitiveM ∷
      PolyStateT (LamIfContext val)
      (NondetJoinT
      (StateT (LamIfStores val)
      ID)) a
  }
  deriving (Functor,Monad,MonadBot,MonadJoin,MonadJoinLattice)

isoFlowInsensitiveM 
  ∷ FlowInsensitiveM val a 
  ⇄ PolyStateT (LamIfContext val) (NondetJoinT (StateT (LamIfStores val) ID)) a
isoFlowInsensitiveM = Iso runFlowInsensitiveM FlowInsensitiveM

isoFlowInsensitiveM2 
   ∷ FlowInsensitiveM val 
  ↝⇄ PolyStateT (LamIfContext val) (NondetJoinT (StateT (LamIfStores val) ID))
isoFlowInsensitiveM2 = iso2FromIso isoFlowInsensitiveM

instance (Join val) ⇒ MonadState (LamIfState val) (FlowInsensitiveM val) where
  stateE ∷ StateT (LamIfState val) (FlowInsensitiveM val) ↝ FlowInsensitiveM val
  stateE = 
    FlowInsensitiveM
    ∘ PolyStateT
    ∘ fmap stateE
    ∘ stateE
    ∘ fmap stateCommute
    ∘ splitState
    ∘ mapState isoSplitLamIfState
    ∘ fmap (runPolyStateT ∘ runFlowInsensitiveM)
  stateI ∷ FlowInsensitiveM val ↝ StateT (LamIfState val) (FlowInsensitiveM val)
  stateI =
    fmap (FlowInsensitiveM ∘ PolyStateT)
    ∘ mapState (sym isoSplitLamIfState)
    ∘ mergeState
    ∘ fmap stateCommute
    ∘ stateI
    ∘ fmap stateI
    ∘ runPolyStateT
    ∘ runFlowInsensitiveM

instance (Join val) ⇒ GaloisTransformer (FlowInsensitiveΣᵇ val) (FlowInsensitiveM val) where
  αGT = isoαGT isoFlowInsensitiveΣᵇ2 isoFlowInsensitiveM2
  γGT = isoγGT isoFlowInsensitiveΣᵇ2 isoFlowInsensitiveM2

instance (POrd val,JoinLattice val,Val val) ⇒ 
  MonadLamIf val (FlowInsensitiveM val)

instance (Ord val,POrd val,JoinLattice val,Difference val,Val val,Pretty val) ⇒ 
  ExecutionLamIf val 
  (InjectLamIf val)
  (FlowInsensitiveΣᵇ val)
  (FlowInsensitiveM val)

-- # Monad Parameters

data MonadParam where
  MonadParam ∷ 
    ∀ val ς' ς m. 
    P m 
    → ς Exp ⇄ ς' Exp
    → (ς Exp → Doc)
    → W (ExecutionLamIf val (InjectLamIf val) ς' m,LFPLamIf ς)
    → MonadParam

pathSensitive ∷ DomainParam → MonadParam
pathSensitive (DomainParam (P ∷ P val) W) = 
  MonadParam (P ∷ P (PathSensitiveM val)) isoPathSensitiveΣ (pretty ∘ mapKeyJoin varAddrName ∘ joins ∘ mapSet (store ∘ snd) ∘ runPathSensitiveΣ) W

flowSensitive ∷ DomainParam → MonadParam
flowSensitive (DomainParam (P ∷ P val) W) = 
  MonadParam (P ∷ P (FlowSensitiveM val)) isoFlowSensitiveΣ (pretty ∘ mapKeyJoin varAddrName ∘ storesStore ∘ joins ∘ values ∘ runFlowSensitiveΣ) W

flowInsensitive ∷ DomainParam → MonadParam
flowInsensitive (DomainParam (P ∷ P val) W) = 
  MonadParam (P ∷ P (FlowInsensitiveM val)) isoFlowInsensitiveΣ (pretty ∘ mapKeyJoin varAddrName ∘ storesStore ∘ snd ∘ runFlowInsensitiveΣ) W
