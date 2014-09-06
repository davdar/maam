module MAAM.Instances.MonadStep where

import FP
import MAAM.Classes.MonadStep

-- ID {{{

instance MonadStep ID where
  type SS ID = ID
  type SSC ID = Universal
  mstep :: (SSC ID a, SSC ID b) => (a -> ID b) -> (SS ID a -> SS ID b)
  mstep f = f . runID
  munit :: (SSC ID a) => P ID -> a -> SS ID a
  munit P = ID

-- }}}

-- State {{{

newtype PairWith s a = PairWith { runPairWith :: (a, s) }
  deriving (Eq, Ord, PartialOrder, HasBot, JoinLattice)
mapPairWith :: ((a, s) -> (b, s)) -> PairWith s a -> PairWith s b
mapPairWith f = PairWith . f . runPairWith
mapPairWithM :: (Functor m) => ((a, s) -> m (b, s)) -> PairWith s a -> m (PairWith s b)
mapPairWithM f = map PairWith . f . runPairWith
instance Functor (PairWith s) where
  map = mapPairWith . mapFst
instance FunctorM (PairWith s) where
  mapM = mapPairWithM . mapFstM
instance (MonadStep m, Functor m, HasBot s) => MonadStep (StateT s m) where
  type SS (StateT s m) = SS m :.: PairWith s
  type SSC (StateT s m) = SSC m ::.:: PairWith s
  mstep :: forall a b. (SSC (StateT s m) a, SSC (StateT s m) b) => (a -> StateT s m b) -> (SS (StateT s m) a -> SS (StateT s m) b)
  mstep f = mapCompose $
     mstep $ \ (runPairWith -> (a, s)) -> PairWith ^$ unStateT (f a) s
  munit :: forall a. (SSC (StateT s m) a) => P (StateT s m) -> a -> SS (StateT s m) a
  munit P = Compose . munit (P :: P m) . PairWith . (, bot)

-- }}}

-- Flow Insensitive {{{

instance (MonadStep m, Functor m, Functorial JoinLattice m) => MonadStep (ListSetT m) where
  type SS (ListSetT m) = SS m :.: Set
  type SSC (ListSetT m) = Ord ::*:: (SSC m ::.:: Set)
  mstep :: (SSC (ListSetT m) a, SSC (ListSetT m) b) => (a -> ListSetT m b) -> SS (ListSetT m) a -> SS (ListSetT m) b
  mstep f = mapCompose $ mstep $ map sset . runListSetT . msums . map f . toList
  munit :: (SSC (ListSetT m) a) => P (ListSetT m) -> a -> SS (ListSetT m) a
  munit P = Compose . munit (P :: P m) . cunit

instance (MonadStep m, Functorial JoinLattice m) => MonadStep (SetT m) where
  type SS (SetT m) = SS m :.: Set
  type SSC (SetT m) = Ord ::*:: (SSC m ::.:: Set)
  mstep :: (SSC (SetT m) a, SSC (SetT m) b) => (a -> SetT m b) -> SS (SetT m) a -> SS (SetT m) b
  mstep f = mapCompose $ mstep $ runSetT . msums . map f . toList
  munit :: (SSC (SetT m) a) => P (SetT m) -> a -> SS (SetT m) a
  munit P = Compose . munit (P :: P m) . cunit

-- }}}

-- Flow Sensitive, Path Insensitive {{{

newtype ForkLT m a = ForkLT { runForkLT :: ListSetT m a }
  deriving (Unit, Functor)
deriving instance (Monad m, Functorial JoinLattice m) => Applicative (ForkLT m)
deriving instance (Bind m, Functorial JoinLattice m) => Bind (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m) => Product (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m) => Monad (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m) => MonadZero (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m) => MonadPlus (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m, MonadStateE s m, JoinLattice s) => MonadStateE s (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m, MonadStateI s m, JoinLattice s) => MonadStateI s (ForkLT m)
deriving instance (Monad m, Functorial JoinLattice m, MonadState s m, JoinLattice s) => MonadState s (ForkLT m)
instance (MonadStep m, Functorial JoinLattice m, CFunctorM (SSC m) (SS m)) => MonadStep (ForkLT m) where
  type SS (ForkLT m) = Set :.: SS m
  type SSC (ForkLT m) = (Ord ::.:: SS m) ::*:: SSC m ::*:: (SSC m ::.:: ListSet)
  mstep :: forall a b. (SSC (ForkLT m) a, SSC (ForkLT m) b) => (a -> ForkLT m b) -> (SS (ForkLT m) a -> SS (ForkLT m) b)
  mstep f = mapCompose $ extend $ fromList . runListSet . csequence . mstep (runListSetT . runForkLT . f)
  munit :: (SSC (ForkLT m) a) => P (ForkLT m) -> a -> SS (ForkLT m) a
  munit P = Compose . ssingleton . munit (P :: P m)

-- }}}
