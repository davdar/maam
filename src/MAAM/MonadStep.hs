module MAAM.MonadStep where

import FP

class MonadStep ς m | m -> ς where
  mstepγ :: (a -> m b) -> ς a -> ς b

-- Identity
instance MonadStep ID ID where
  mstepγ :: (a -> ID b) -> (ID a -> ID b)
  mstepγ = extend

-- State
instance (MonadStep ς m, Functor m) => MonadStep (ς :.: (,) 𝓈) (StateT 𝓈 m) where
  mstepγ :: (a -> StateT 𝓈 m b) -> ((ς :.: (,) 𝓈) a -> (ς :.: (,) 𝓈)  b)
  mstepγ f = onComposeIso $ mstepγ $ \ (s, a) -> unStateT (f a) s
deriving instance (MonadStep ς m, Functor m) => MonadStep (ς :.: (,) 𝓈1) (AddStateT 𝓈12 𝓈1 m)

-- Flow Insensitive
instance (MonadStep ς m, Functorial JoinLattice m) => MonadStep (ς :.: ListSet) (ListSetT m) where
  mstepγ :: forall a b. (a -> ListSetT m b) -> (ς :.: ListSet) a -> (ς :.: ListSet) b
  mstepγ f = 
    with (functorial :: W (JoinLattice (m (ListSet b)))) $
    onComposeIso $ (mstepγ :: forall a' b'. (a' -> m b') -> (ς a' -> ς b')) $ joins . map (unListSetT . f)

-- Flow Insensitive with top
instance (MonadStep ς m, Functorial JoinLattice m, Unit m) => MonadStep (ς :.: ListSetWithTop) (ListSetWithTopT m) where
  mstepγ :: forall a b. (a -> ListSetWithTopT m b) -> (ς :.: ListSetWithTop) a -> (ς :.: ListSetWithTop) b
  mstepγ f = 
    with (functorial :: W (JoinLattice (m (ListSetWithTop b)))) $
    onComposeIso $ (mstepγ :: forall a' b'. (a' -> m b') -> (ς a' -> ς b')) $ listSetWithTopElim (unit top) joins . map (unListSetWithTopT . f)

-- Flow Sensitive
instance (MonadStep ς m, Commute ς ListSet, Functorial JoinLattice ς) => MonadStep (ListSet :.: ς) (ListSetT m) where
  mstepγ :: forall a b. (a -> ListSetT m b) -> (ListSet :.: ς) a -> (ListSet :.: ς) b
  mstepγ f = 
    with (functorial :: W (JoinLattice (ς (ListSet b)))) $
    onComposeIso $ commute . joins . map (mstepγ $ unListSetT . f)

-- Flow Sensitive with top
instance (MonadStep ς m, Commute ς ListSetWithTop, Functorial JoinLattice ς, Unit ς) => MonadStep (ListSetWithTop :.: ς) (ListSetWithTopT m) where
  mstepγ :: forall a b. (a -> ListSetWithTopT m b) -> (ListSetWithTop :.: ς) a -> (ListSetWithTop :.: ς) b
  mstepγ f = 
    with (functorial :: W (JoinLattice (ς (ListSetWithTop b)))) $
    onComposeIso $ commute . listSetWithTopElim (unit top) joins . map (mstepγ $ unListSetWithTopT . f)

instance Commute ID ListSet where
  commute :: ID (ListSet a) -> ListSet (ID a)
  commute = map ID . unID

instance Commute ((,) 𝓈) ListSet where
  commute :: (𝓈, ListSet a) -> ListSet (𝓈, a)
  commute (s, xs) = map (s,) xs

instance (Commute t ListSet, Commute u ListSet, Functor t) => Commute (t :.: u) ListSet where
  commute :: (t :.: u) (ListSet a) -> ListSet ((t :.: u) a)
  commute = map Compose . commute . map commute . unCompose

newtype IsoMonadStep ς1 ς2 m a = IsoMonadStep { runIsoMonadStep :: m a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadBot, MonadPlus, MonadTop
    , MonadState s
    )
instance (MonadStep ς2 m, Isomorphism2 ς1 ς2) => MonadStep ς1 (IsoMonadStep ς1 ς2 m) where
  mstepγ :: (a -> IsoMonadStep ς1 ς2 m b) -> (ς1 a -> ς1 b)
  mstepγ f = isofrom2 . mstepγ (runIsoMonadStep . f) . isoto2
