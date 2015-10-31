module MAAM.GaloisTransformer where

import FP

class GaloisTransformer ς m | m → ς where
  αGT ∷ ∀ a b. (ς a → ς b) → (a → m b)
  γGT ∷ ∀ a b. (a → m b) → (ς a → ς b)

class Inject ι ς | ς → ι where
  inject ∷ ι a → ς a

-- # Identity

instance GaloisTransformer ID ID where
  αGT ∷ ∀ a b. (ID a → ID b) → (a → ID b)
  αGT f = f ∘ ID
  γGT ∷ ∀ a b. (a → ID b) → (ID a → ID b)
  γGT f = f ∘ runID

instance Inject ID ID where
  inject = id

-- # Galois Transformers

-- ## Monad Transformers

-- StateT defined in FP.Prelude.Effects and FP.Prelude.Monads

isoToStateTMorph ∷ ((a,s) → m (b,s)) → (a → StateT s m b)
isoToStateTMorph f x = StateT $ \ s → f (x,s)

isoFromStateTMorph ∷ (a → StateT s m b) → ((a,s) → m (b,s))
isoFromStateTMorph f (x,s) = runStateT (f x) s

-- PolyStateT

-- Has a polymorphic (rather than functorial) implementation for POrd and
-- JoinLattice. This goes "on top" of nondeterminism monads, whereas the
-- builtin state goes "on bottom".

newtype PolyStateT s m a = PolyStateT { runPolyStateT ∷ StateT s m a }
  deriving (Functor,Monad,MonadBot,MonadJoin,MonadJoinLattice,MonadState s)

isoToPolyStateTMorph ∷ ((a,s) → m (b,s)) → (a → PolyStateT s m b)
isoToPolyStateTMorph f x = PolyStateT $ StateT $ \ s → f (x,s)

isoFromPolyStateTMorph ∷ (a → PolyStateT s m b) → ((a,s) → m (b,s))
isoFromPolyStateTMorph f (x,s) = runStateT (runPolyStateT (f x)) s

instance (Polymorphic JoinLattice m) ⇒ Bot (PolyStateT s m a) where
  bot =
    with (polymorphic ∷ W (JoinLattice (m (a,s)))) $
    PolyStateT $ StateT bot
instance (Polymorphic JoinLattice m) ⇒ Join (PolyStateT s m a) where
  PolyStateT (StateT x) ⊔ PolyStateT (StateT y) =
    with (polymorphic ∷ W (JoinLattice (m (a,s)))) $
    PolyStateT $ StateT $ x ⊔ y
instance (Polymorphic JoinLattice m) ⇒ JoinLattice (PolyStateT s m a)
instance (Polymorphic JoinLattice m) ⇒ Polymorphic JoinLattice (PolyStateT s m) where polymorphic = W

-- NondetT defined in FP.Prelude.Effects and FP.Prelude.Monads

isoToNondetJoinTMorph ∷ (a → m (𝒫ᵇ b)) → (a → NondetJoinT m b)
isoToNondetJoinTMorph f = NondetJoinT ∘ f

isoFromNondetJoinTMorph ∷ (a → NondetJoinT m b) → (a → m (𝒫ᵇ b))
isoFromNondetJoinTMorph f = runNondetJoinT ∘ f

-- FlowT defined in FP.Prelude.Effects and FP.Prelude.Monads

isoToFlowJoinTMorph ∷ ((a,s) → m (b ⇰♭⊔ s)) → (a → FlowJoinT s m b)
isoToFlowJoinTMorph f x = FlowJoinT $ \ s → f (x,s)

isoFromFlowJoinTMorph ∷ (a → FlowJoinT s m b) → ((a,s) → m (b ⇰♭⊔ s))
isoFromFlowJoinTMorph f (x,s) = runFlowJoinT (f x) s

-- ## Transition Systems

newtype StateΠ s ς a = StateΠ { runStateΠ ∷ ς (a,s) }
makePrettyUnion ''StateΠ
instance (OrdFunctorial POrd ς,POrd s,POrd a,Ord s,Ord a) ⇒ POrd (StateΠ s ς a) where
  (⊑⊒) =
    with (ordFunctorial ∷ W (POrd (ς (a,s)))) $
    (⊑⊒) `on` runStateΠ
instance (OrdFunctorial POrd ς,POrd s,Ord s) ⇒ OrdFunctorial POrd (StateΠ s ς) where ordFunctorial = W
instance (Functorial JoinLattice ς,JoinLattice s,JoinLattice a) ⇒ Bot (StateΠ s ς a) where
  bot =
    with (functorial ∷ W (JoinLattice (ς (a,s)))) $
    StateΠ bot
instance (Functorial JoinLattice ς,JoinLattice s,JoinLattice a) ⇒ Join (StateΠ s ς a) where
  StateΠ x ⊔ StateΠ y =
    with (functorial ∷ W (JoinLattice (ς (a,s)))) $
    StateΠ $ x ⊔ y
instance (Functorial JoinLattice ς,JoinLattice s,JoinLattice a) ⇒ JoinLattice (StateΠ s ς a)
instance (Functorial JoinLattice ς,JoinLattice s) ⇒ Functorial JoinLattice (StateΠ s ς) where functorial = W
instance (Difference (ς (a,s))) ⇒ Difference (StateΠ s ς a) where
  StateΠ x ⊟ StateΠ y = StateΠ (x ⊟ y)

instance (Functor ς) ⇒ Functor (StateΠ s ς) where
  map f = StateΠ ∘ map (mapFst f) ∘ runStateΠ

isoToStateΠMorph ∷ (ς (a,s) → ς (b,s)) → (StateΠ s ς a → StateΠ s ς b)
isoToStateΠMorph f = StateΠ ∘ f ∘ runStateΠ

isoFromStateΠMorph ∷ (StateΠ s ς a → StateΠ s ς b) → (ς (a,s) → ς (b,s))
isoFromStateΠMorph f = runStateΠ ∘ f ∘ StateΠ

newtype PolyStateΠ s ς a = PolyStateΠ { runPolyStateΠ ∷ ς (a,s) }
makePrettyUnion ''PolyStateΠ

isoPolyStateΠ ∷ PolyStateΠ s ς a ⇄ ς (a,s)
isoPolyStateΠ = Iso runPolyStateΠ PolyStateΠ

instance (OrdPolymorphic POrd ς,Ord s,Ord a) ⇒ POrd (PolyStateΠ s ς a) where
  (⊑⊒) =
    with (ordPolymorphic ∷ W (POrd (ς (a,s)))) $
    (⊑⊒) `on` runPolyStateΠ
instance (OrdPolymorphic POrd ς,Ord s) ⇒ OrdPolymorphic POrd (PolyStateΠ s ς) where ordPolymorphic = W
instance (Polymorphic JoinLattice ς) ⇒ Bot (PolyStateΠ s ς a) where
  bot =
    with (polymorphic ∷ W (JoinLattice (ς (a,s)))) $
    PolyStateΠ bot
instance (Polymorphic JoinLattice ς) ⇒ Join (PolyStateΠ s ς a) where
  PolyStateΠ x ⊔ PolyStateΠ y =
    with (polymorphic ∷ W (JoinLattice (ς (a,s)))) $
    PolyStateΠ $ x ⊔ y
instance (Polymorphic JoinLattice ς) ⇒ JoinLattice (PolyStateΠ s ς a)
instance (Polymorphic JoinLattice ς) ⇒ Polymorphic JoinLattice (PolyStateΠ s ς) where polymorphic = W
instance (Difference (ς (a,s))) ⇒ Difference (PolyStateΠ s ς a) where
  PolyStateΠ x ⊟ PolyStateΠ y = PolyStateΠ (x ⊟ y)

instance (Functor ς) ⇒ Functor (PolyStateΠ s ς) where
  map f = PolyStateΠ ∘ map (mapFst f) ∘ runPolyStateΠ

isoToPolyStateΠMorph ∷ (ς (a,s) → ς (b,s)) → (PolyStateΠ s ς a → PolyStateΠ s ς b)
isoToPolyStateΠMorph f = PolyStateΠ ∘ f ∘ runPolyStateΠ

isoFromPolyStateΠMorph ∷ (PolyStateΠ s ς a → PolyStateΠ s ς b) → (ς (a,s) → ς (b,s))
isoFromPolyStateΠMorph f = runPolyStateΠ ∘ f ∘ PolyStateΠ

newtype NondetJoinΠ ς a = NondetJoinΠ { runNondetJoinΠ ∷ ς (𝒫ᵇ a) }
makePrettyUnion ''NondetJoinΠ

isoNondetJoinΠ ∷ NondetJoinΠ ς a ⇄ ς (𝒫ᵇ a)
isoNondetJoinΠ = Iso runNondetJoinΠ NondetJoinΠ

instance (OrdFunctorial POrd ς,Ord a) ⇒ POrd (NondetJoinΠ ς a) where
  (⊑⊒) =
    with (ordFunctorial ∷ W (POrd (ς (𝒫ᵇ a)))) $
    (⊑⊒) `on` runNondetJoinΠ
instance (OrdFunctorial POrd ς) ⇒ OrdPolymorphic POrd (NondetJoinΠ ς) where ordPolymorphic = W
instance (Functorial JoinLattice ς) ⇒ Bot (NondetJoinΠ ς a) where
  bot =
    with (functorial ∷ W (JoinLattice (ς (𝒫ᵇ a)))) $
    NondetJoinΠ bot
instance (Functorial JoinLattice ς) ⇒ Join (NondetJoinΠ ς a) where
  NondetJoinΠ x ⊔ NondetJoinΠ y =
    with (functorial ∷ W (JoinLattice (ς (𝒫ᵇ a)))) $
    NondetJoinΠ $ x ⊔ y
instance (Functorial JoinLattice ς) ⇒ JoinLattice (NondetJoinΠ ς a)
instance (Functorial JoinLattice ς) ⇒ Polymorphic JoinLattice (NondetJoinΠ ς) where polymorphic = W
instance (Difference (ς (𝒫ᵇ a))) ⇒ Difference (NondetJoinΠ ς a) where
  NondetJoinΠ x ⊟ NondetJoinΠ y = NondetJoinΠ $ x ⊟ y

isoToNondetJoinΠMorph ∷ (ς (𝒫ᵇ a) → ς (𝒫ᵇ b)) → (NondetJoinΠ ς a → NondetJoinΠ ς b)
isoToNondetJoinΠMorph f = NondetJoinΠ ∘ f ∘ runNondetJoinΠ

isoFromNondetJoinΠMorph ∷ (NondetJoinΠ ς a → NondetJoinΠ ς b) → (ς (𝒫ᵇ a) → ς (𝒫ᵇ b))
isoFromNondetJoinΠMorph f = runNondetJoinΠ ∘ f ∘ NondetJoinΠ

newtype FlowJoinΠ s ς a = FlowJoinΠ { runFlowJoinΠ ∷ ς (a ⇰♭⊔ s) }
makePrettyUnion ''FlowJoinΠ

instance (OrdFunctorial POrd ς,POrd s,JoinLattice s,Ord s,Ord a) ⇒ POrd (FlowJoinΠ s ς a) where
  (⊑⊒) =
    with (ordFunctorial ∷ W (POrd (ς (a ⇰♭⊔ s)))) $
    (⊑⊒) `on` runFlowJoinΠ
instance (OrdFunctorial POrd ς,POrd s,JoinLattice s,Ord s) ⇒ OrdPolymorphic POrd (FlowJoinΠ s ς) where ordPolymorphic = W
instance (Functorial JoinLattice ς) ⇒ Bot (FlowJoinΠ s ς a) where
  bot =
    with (functorial ∷ W (JoinLattice (ς (a ⇰♭⊔ s)))) $
    FlowJoinΠ bot
instance (Functorial JoinLattice ς) ⇒ Join (FlowJoinΠ s ς a) where
  FlowJoinΠ x ⊔ FlowJoinΠ y =
    with (functorial ∷ W (JoinLattice (ς (a ⇰♭⊔ s)))) $
    FlowJoinΠ $ x ⊔ y
instance (Functorial JoinLattice ς) ⇒ JoinLattice (FlowJoinΠ s ς a)
instance (Functorial JoinLattice ς) ⇒ Polymorphic JoinLattice (FlowJoinΠ s ς) where polymorphic = W
instance (Difference (ς (a ⇰♭⊔ s))) ⇒ Difference (FlowJoinΠ s ς a) where
  FlowJoinΠ x ⊟ FlowJoinΠ y = FlowJoinΠ $ x ⊟ y

isoToFlowJoinΠMorph ∷ (ς (a ⇰♭⊔ s) → ς (b ⇰♭⊔ s)) → (FlowJoinΠ s ς a → FlowJoinΠ s ς b)
isoToFlowJoinΠMorph f = FlowJoinΠ ∘ f ∘ runFlowJoinΠ

isoFromFlowJoinΠMorph ∷ (FlowJoinΠ s ς a → FlowJoinΠ s ς b) → (ς (a ⇰♭⊔ s) → ς (b ⇰♭⊔ s))
isoFromFlowJoinΠMorph f = runFlowJoinΠ ∘ f ∘ FlowJoinΠ

-- ## Injections

newtype StateI s ι a = StateI { runStateI ∷ ι (a,s) }
isoStateI ∷ StateI s ι a ⇄ ι (a,s)
isoStateI = Iso runStateI StateI

type NondetJoinI ι = ι
type FlowJoinI = StateI

-- ## Galois Transformers Instances

instance 
  (GaloisTransformer ς m) 
  ⇒ 
  GaloisTransformer (StateΠ s ς) (StateT s m) where
    αGT ∷ ∀ a b. (StateΠ s ς a → StateΠ s ς b) → (a → StateT s m b)
    αGT (isoFromStateΠMorph → f) = isoToStateTMorph $ αGT f
    γGT ∷ ∀ a b. (a → StateT s m b) → (StateΠ s ς a → StateΠ s ς b)
    γGT (isoFromStateTMorph → f) = isoToStateΠMorph $ γGT f

instance 
  (GaloisTransformer ς m) 
  ⇒ 
  GaloisTransformer (PolyStateΠ s ς) (PolyStateT s m) where
    αGT ∷ ∀ a b. (PolyStateΠ s ς a → PolyStateΠ s ς b) → (a → PolyStateT s m b)
    αGT (isoFromPolyStateΠMorph → f) = isoToPolyStateTMorph $ αGT f
    γGT ∷ ∀ a b. (a → PolyStateT s m b) → (PolyStateΠ s ς a → PolyStateΠ s ς b)
    γGT (isoFromPolyStateTMorph → f) = isoToPolyStateΠMorph $ γGT f

instance 
  (GaloisTransformer ς m,Functorial JoinLattice m) 
  ⇒ 
  GaloisTransformer (NondetJoinΠ ς) (NondetJoinT m) where
    αGT ∷ ∀ a b. (NondetJoinΠ ς a → NondetJoinΠ ς b) → (a → NondetJoinT m b)
    αGT (isoFromNondetJoinΠMorph → f) = isoToNondetJoinTMorph $ αGT f ∘ return
    γGT ∷ ∀ a b. (a → NondetJoinT m b) → (NondetJoinΠ ς a → NondetJoinΠ ς b)
    γGT (isoFromNondetJoinTMorph → f) = 
      with (functorial ∷ W (JoinLattice (m (𝒫ᵇ b)))) $
      isoToNondetJoinΠMorph $ γGT $ joins ∘ map f

instance 
  (GaloisTransformer ς m,Functorial JoinLattice m,JoinLattice s) 
  ⇒ 
  GaloisTransformer (FlowJoinΠ s ς) (FlowJoinT s m) where
    αGT ∷ ∀ a b. (FlowJoinΠ s ς a → FlowJoinΠ s ς b) → (a → FlowJoinT s m b)
    αGT (isoFromFlowJoinΠMorph → f) = isoToFlowJoinTMorph $ αGT f ∘ lazyDictJoin ∘ singleFold
    γGT ∷ ∀ a b. (a → FlowJoinT s m b) → (FlowJoinΠ s ς a → FlowJoinΠ s ς b)
    γGT (isoFromFlowJoinTMorph → f) = 
      with (functorial ∷ W (JoinLattice (m (b ⇰♭⊔ s)))) $
      isoToFlowJoinΠMorph $ γGT $ \ xss → joins $ map f $ list xss

isoαGT ∷ (GaloisTransformer ς₁ m₁) ⇒ ς₂ ↝⇄ ς₁ → m₂ ↝⇄ m₁ → ∀ a b. (ς₂ a → ς₂ b) → (a → m₂ b)
isoαGT isomorphicς isomorphicm f = isoFrom2 isomorphicm ∘ αGT (isoTo2 isomorphicς ∘ f ∘ isoFrom2 isomorphicς)

isoγGT ∷ (GaloisTransformer ς₁ m₁) ⇒ ς₂ ↝⇄ ς₁ → m₂ ↝⇄ m₁ → ∀ a b. (a → m₂ b) → (ς₂ a → ς₂ b)
isoγGT isomorphicς isomorphicm f = isoFrom2 isomorphicς ∘ γGT (isoTo2 isomorphicm ∘ f) ∘ isoTo2 isomorphicς

-- ## Injection Instances

instance (Inject ι ς) ⇒ Inject (StateI s ι) (StateΠ s ς) where
  inject ∷ ∀ a. StateI s ι a → StateΠ s ς a
  inject (StateI ιas) = StateΠ $ inject ιas

instance (Inject ι ς) ⇒ Inject (StateI s ι) (PolyStateΠ s ς) where
  inject ∷ ∀ a. StateI s ι a → PolyStateΠ s ς a
  inject (StateI ιas) = PolyStateΠ $ inject ιas

instance (Inject ι ς,Functor ς) ⇒ Inject ι (NondetJoinΠ ς) where
  inject ∷ ∀ a. ι a → NondetJoinΠ ς a
  inject aI = NondetJoinΠ $ single ^$ inject aI

instance (Inject ι ς,Functor ς) ⇒ Inject (StateI s ι) (FlowJoinΠ s ς) where
  inject ∷ ∀ a. StateI s ι a → FlowJoinΠ s ς a
  inject (StateI ιas) = FlowJoinΠ $ map single $ inject ιas

isoInject ∷ (Inject ι₁ ς₁) ⇒ ι₂ ↝⇄ ι₁ → ς₂ ↝⇄ ς₁ → ∀ a. ι₂ a → ς₂ a
isoInject isomorphicι isomorphicς = isoFrom2 isomorphicς ∘ inject ∘ isoTo2 isomorphicι
