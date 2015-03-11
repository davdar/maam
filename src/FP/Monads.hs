module FP.Monads where

import FP.Core

---------------------
-- Monadic Effects --
---------------------

-- ID {{{

newtype ID a = ID { unID :: a }
  deriving
  ( Eq, Ord
  , PartialOrder
  , Monoid
  , Bot
  , Join
  , JoinLattice
  )

instance Unit ID where unit = ID
instance Functor ID where map f = ID . f . unID
instance FunctorM ID where mapM f = map ID . f . unID
instance Product ID where aM <*> bM = ID $ (unID aM, unID bM)
instance Applicative ID where fM <@> aM = ID $ unID fM $ unID aM
instance Bind ID where aM >>= k = k $ unID aM
instance Monad ID
instance Functorial Bot ID where functorial = W
instance Functorial Join ID where functorial = W
instance Functorial JoinLattice ID where functorial = W
instance Functorial Monoid ID where functorial = W

newtype IDT m a = IDT { unIDT :: m a }

-- }}}

-- MaybeT {{{

maybeCommute :: (Functor m) => MaybeT (MaybeT m) ~> MaybeT (MaybeT m)
maybeCommute aMM = MaybeT $ MaybeT $ ff ^$ unMaybeT $ unMaybeT aMM
  where
    ff Nothing = Just Nothing
    ff (Just Nothing) = Nothing
    ff (Just (Just a)) = Just (Just a)
  
instance (Unit m) => Unit (MaybeT m) where
  unit = MaybeT . unit . Just
instance (Functor m) => Functor (MaybeT m) where
  map f = MaybeT . f ^^. unMaybeT
instance (Functor m, Product m) => Product (MaybeT m) where
  aM1 <*> aM2 = MaybeT $ uncurry ff ^$ unMaybeT aM1 <*> unMaybeT aM2
    where
      ff Nothing _ = Nothing
      ff _ Nothing = Nothing
      ff (Just a1) (Just a2) = Just (a1, a2)
instance (Functor m, Applicative m) => Applicative (MaybeT m) where
  fM <@> aM = MaybeT $ ff ^@ unMaybeT fM <$> unMaybeT aM
    where
      ff Nothing _ = Nothing
      ff _ Nothing = Nothing
      ff (Just f) (Just a) = Just $ f a
instance (Monad m) => Bind (MaybeT m) where
  aM >>= k = MaybeT $ do
    aM' <- unMaybeT aM
    case aM' of
      Nothing -> return Nothing
      Just a -> unMaybeT $ k a
instance (Monad m) => Monad (MaybeT m) where

instance FunctorUnit2 MaybeT where
  funit2 = MaybeT .^ Just
instance FunctorJoin2 MaybeT where
  fjoin2 = MaybeT . ff ^. unMaybeT . unMaybeT
    where
      ff Nothing = Nothing
      ff (Just aM) = aM
instance FunctorFunctor2 MaybeT where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> MaybeT m ~> MaybeT n
  fmap2 f = MaybeT . f . unMaybeT

instance (Monad m) => MonadMaybeI (MaybeT m) where
  maybeI :: MaybeT m ~> MaybeT (MaybeT m)
  maybeI = maybeCommute . funit2
instance (Monad m) => MonadMaybeE (MaybeT m) where
  maybeE :: MaybeT (MaybeT m) ~> MaybeT m
  maybeE = fjoin2 . maybeCommute

-- }}}

-- ErrorT {{{

mapError :: (Functor m) => (e1 -> e2) -> ErrorT e1 m a -> ErrorT e2 m a
mapError f = ErrorT . mapInl f ^. unErrorT

errorCommute :: (Functor m) => ErrorT e (ErrorT e m) ~> ErrorT e (ErrorT e m)
errorCommute = ErrorT . ErrorT . ff ^. unErrorT . unErrorT
  where
    ff (Inl e) = Inr (Inl e)
    ff (Inr (Inl e)) = Inl e
    ff (Inr (Inr a)) = Inr $ Inr a

instance (Unit m) => Unit (ErrorT e m) where
  unit a = ErrorT $ unit $ Inr a
instance (Functor m) => Functor (ErrorT e m) where
  map f aM = ErrorT $ mapInr f ^$ unErrorT aM
instance (Functor m, Product m) => Product (ErrorT e m) where
  aM1 <*> aM2 = ErrorT $ ff ^$ unErrorT aM1 <*> unErrorT aM2
    where
      ff (Inl e, _) = Inl e
      ff (_, Inl e) = Inl e
      ff (Inr a, Inr b) = Inr (a, b)
instance (Functor m, Applicative m) => Applicative (ErrorT e m) where
  fM <@> aM = ErrorT $ ff ^@ unErrorT fM <$> unErrorT aM
    where
      ff (Inl e) _ = Inl e
      ff _ (Inl e) = Inl e
      ff (Inr f) (Inr a) = Inr $ f a
instance (Unit m, Bind m) => Bind (ErrorT e m) where
  aM >>= k = ErrorT $ do
    aeM <- unErrorT aM
    case aeM of
      Inl e -> unit $ Inl e
      Inr a -> unErrorT $ k a
instance (Monad m) => Monad (ErrorT e m) where
instance FunctorUnit2 (ErrorT e) where
  funit2 :: (Functor m) => m ~> ErrorT e m
  funit2 aM = ErrorT $ Inr ^$ aM
instance FunctorJoin2 (ErrorT e) where
  fjoin2 :: (Functor m) => ErrorT e (ErrorT e m) ~> ErrorT e m
  fjoin2 = ErrorT . ff ^. unErrorT . unErrorT
    where
      ff (Inl e) = Inl e
      ff (Inr ea) = ea
instance FunctorFunctor2 (ErrorT e) where
  fmap2 :: (Functor m, Functor n) => m ~> n -> ErrorT e m ~> ErrorT e n
  fmap2 f = ErrorT . f . unErrorT

instance (Monad m) => MonadErrorI e (ErrorT e m) where
  errorI :: ErrorT e m ~> ErrorT e (ErrorT e m)
  errorI = errorCommute . funit2
instance (Monad m) => MonadErrorE e (ErrorT e m) where
  errorE :: ErrorT e (ErrorT e m) ~> ErrorT e m
  errorE = fjoin2 . errorCommute
instance (Monad m) => MonadError e (ErrorT e m) where

-- }}}

-- ReaderT {{{

type Reader r = ReaderT r ID

runReader :: r -> Reader r a -> a
runReader r = unID . runReaderT r

readerCommute :: ReaderT r1 (ReaderT r2 m) ~> ReaderT r2 (ReaderT r1 m)
readerCommute aMM = ReaderT $ \ r2 -> ReaderT $ \ r1 -> runReaderT r2 $ runReaderT r1 aMM

instance (Unit m) => Unit (ReaderT r m) where
  unit = ReaderT . const . unit
instance (Functor m) => Functor (ReaderT r m) where
  map f = ReaderT . f ^^. unReaderT
instance (Product m) => Product (ReaderT r m) where
  aM1 <*> aM2 = ReaderT $ \ r ->
    runReaderT r aM1 <*> runReaderT r aM2
instance (Applicative m) => Applicative (ReaderT r m) where
  fM <@> aM = ReaderT $ \ r ->
    runReaderT r fM <@> runReaderT r aM
instance (Bind m) => Bind (ReaderT r m) where
  aM >>= k = ReaderT $ \ r -> runReaderT r . k *$ runReaderT r aM
instance (Monad m) => Monad (ReaderT r m) where
instance FunctorUnit2 (ReaderT r) where
  funit2 = ReaderT . const
instance FunctorJoin2 (ReaderT r) where
  fjoin2 aMM = ReaderT $ \ r -> runReaderT r $ runReaderT r aMM
instance FunctorFunctor2 (ReaderT r) where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> (ReaderT r m ~> ReaderT r n)
  fmap2 f aM = ReaderT $ \ r -> f $ runReaderT r aM

instance (Monad m) => MonadReaderI r (ReaderT r m) where
  readerI :: ReaderT r m ~> ReaderT r (ReaderT r m)
  readerI = readerCommute . funit2
instance (Monad m) => MonadReaderE r (ReaderT r m) where
  readerE :: ReaderT r (ReaderT r m) ~> ReaderT r m
  readerE = fjoin2 . readerCommute
instance (Monad m) => MonadReader r (ReaderT r m) where

instance (MonadZero m) => MonadZero (ReaderT r m) where
  mzero = ReaderT $ const mzero
instance (MonadConcat m) => MonadConcat (ReaderT r m) where
  aM1 <++> aM2 = ReaderT $ \ r -> unReaderT aM1 r <++> unReaderT aM2 r

-- }}}

-- WriterT {{{

execWriterT :: (Functor m) => WriterT o m a -> m o
execWriterT = snd ^. unWriterT

mapOutput :: (Functor m) => (o1 -> o2) -> WriterT o1 m a -> WriterT o2 m a
mapOutput f = WriterT . mapSnd f ^. unWriterT

writerCommute :: (Functor m) => WriterT o1 (WriterT o2 m) ~> WriterT o2 (WriterT o1 m)
writerCommute aMM = WriterT $ WriterT $ ff ^$ unWriterT $ unWriterT aMM
  where
    ff ((a, o1), o2) = ((a, o2), o1)

instance (Unit m, Monoid o) => Unit (WriterT o m) where
  unit = WriterT . unit . (,null)
instance (Functor m) => Functor (WriterT o m) where
  map f = WriterT . mapFst f ^. unWriterT
instance (Functor m, Product m, Monoid o) => Product (WriterT o m) where
  aM1 <*> aM2 = WriterT $ ff ^$ unWriterT aM1 <*> unWriterT aM2
    where
      ff ((a1, o1), (a2, o2)) = ((a1, a2), o1 ++ o2)
instance (Functor m, Applicative m, Monoid o) => Applicative (WriterT o m) where
  fM <@> aM = WriterT $ ff2 ^$ ff1 ^@ unWriterT fM <$> unWriterT aM
    where
      ff1 (f, o) = mapFst ((,o) . f)
      ff2 ((a, o1), o2) = (a, o1 ++ o2)
instance (Monad m, Monoid o) => Bind (WriterT o m) where
  aM >>= k = WriterT $ do
    (a, o1) <- unWriterT aM
    (b, o2) <- unWriterT $ k a
    return (b, o1 ++ o2)
instance (Monad m, Monoid o) => Monad (WriterT o m) where
instance (Monoid w) => FunctorUnit2 (WriterT w) where
  funit2 = WriterT .^ (,null)
instance FunctorJoin2 (WriterT w) where
  fjoin2 = fst ^. unWriterT
instance FunctorFunctor2 (WriterT w) where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> (WriterT w m ~> WriterT w n)
  fmap2 f aM = WriterT $ f $ unWriterT aM

instance (Monad m, Monoid o) => MonadWriterI o (WriterT o m) where
  writerI :: WriterT o m ~> WriterT o (WriterT o m)
  writerI = writerCommute . funit2
instance (Monad m, Monoid o) => MonadWriterE o (WriterT o m) where
  writerE :: WriterT o (WriterT o m) ~> WriterT o m
  writerE = fjoin2 . writerCommute
instance (Monad m, Monoid o) => MonadWriter o (WriterT o m) where

instance (MonadZero m, Monoid o) => MonadZero (WriterT o m) where
  mzero = WriterT $ mzero

-- }}}

-- StateT {{{ --

runStateT :: s -> StateT s m a -> m (a, s)
runStateT = flip unStateT

evalStateT :: (Functor m) => s -> StateT s m a -> m a
evalStateT = fst ^.: runStateT

execStateT :: (Functor m) => s -> StateT s m a -> m s
execStateT = snd ^.: runStateT

mapStateT :: (Functor m) => (s1 -> s2) -> (s2 -> s1) -> StateT s1 m a -> StateT s2 m a
mapStateT to from aM = StateT $ \ s2 -> ff ^$ unStateT aM $ from s2
  where ff (a, s1) = (a, to s1)

type State s = StateT s ID

runState :: s -> State s a -> (a, s)
runState = unID .: runStateT

evalState :: s -> State s a -> a
evalState = fst .: runState

execState :: s -> State s a -> s
execState = snd .: runState

stateCommute :: (Functor m) => StateT s1 (StateT s2 m) ~> StateT s2 (StateT s1 m)
stateCommute aMM = StateT $ \ s2 -> StateT $ \ s1 -> ff ^$ runStateT s2 $ runStateT s1 aMM
  where
    ff ((a, s1), s2) = ((a, s2), s1)

stateLens :: (Monad m) => Lens s1 s2 -> StateT s2 m ~> StateT s1 m
stateLens l aM = StateT $ \ s1 -> do
  let s2 = access l s1
  (a, s2') <- unStateT aM s2
  return (a, set l s2' s1)

stateLensE :: (MonadStateE s1 m, Monad m) => Lens s1 s2 -> (StateT s2 m ~> m)
stateLensE = stateE .: stateLens

instance (Unit m) => Unit (StateT s m) where
  unit x = StateT $ \ s -> unit (x, s)
instance (Functor m) => Functor (StateT s m) where
  map f aM = StateT $ \ s -> mapFst f ^$ unStateT aM s
instance (Monad m) => Product (StateT s m) where
  (<*>) = mpair
instance (Monad m) => Applicative (StateT s m) where
  (<@>) = mapply
instance (Bind m) => Bind (StateT s m) where
  aM >>= k = StateT $ \ s -> do
    (a, s') <- unStateT aM s
    unStateT (k a) s'
instance (Monad m) => Monad (StateT s m) where
instance FunctorUnit2 (StateT s) where
  funit2 aM = StateT $ \ s -> (,s) ^$ aM
instance FunctorJoin2 (StateT s) where
  fjoin2 aMM = StateT $ \ s -> runStateT s $ fst ^$ runStateT s aMM
instance FunctorFunctor2 (StateT s) where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> StateT s m ~> StateT s n
  fmap2 f aM = StateT $ f . unStateT aM

instance (MonadZero m) => MonadZero (StateT s m) where
  mzero = StateT $ const mzero
instance (MonadPlus m) => MonadPlus (StateT s m) where
  aM1 <+> aM2 = StateT $ \ s -> unStateT aM1 s <+> unStateT aM2 s
instance (MonadConcat m) => MonadConcat (StateT s m) where
  aM1 <++> aM2 = StateT $ \ s -> unStateT aM1 s <++> unStateT aM2 s

instance (Functorial Monoid m, Monoid s, Monoid a) => Monoid (StateT s m a) where
  null =
    with (functorial :: W (Monoid (m (a, s)))) $
    StateT $ \ _ -> null
  aM1 ++ aM2 =
    with (functorial :: W (Monoid (m (a, s)))) $
    StateT $ \ s -> unStateT aM1 s ++ unStateT aM2 s
instance (Functorial Monoid m, Monoid s) => Functorial Monoid (StateT s m) where
  functorial = W
instance (Functorial Bot m, Bot s, Bot a) => Bot (StateT s m a) where
  bot :: StateT s m a
  bot = 
    with (functorial :: W (Bot (m (a, s)))) $
    StateT $ \ _ -> bot
instance (Functorial Join m, Join s, Join a) => Join (StateT s m a) where
  aM1 \/ aM2 = 
    with (functorial :: W (Join (m (a, s)))) $
    StateT $ \ s -> unStateT aM1 s \/ unStateT aM2 s
instance (Functorial Bot m, Functorial Join m, JoinLattice s, JoinLattice a) => JoinLattice (StateT s m a)
instance (Functorial Bot m, Functorial Join m, JoinLattice s) => Functorial JoinLattice (StateT s m) where functorial = W

instance (Functor m) => MonadStateI s (StateT s m) where
  stateI :: StateT s m ~> StateT s (StateT s m) 
  stateI = stateCommute . funit2
instance (Functor m) => MonadStateE s (StateT s m) where
  stateE :: StateT s (StateT s m) ~> StateT s m
  stateE = fjoin2 . stateCommute
instance (Functor m) => MonadState s (StateT s m) where

-- }}} --

-- AddStateT {{{

newtype AddStateT s12 s1 m a = AddStateT { runAddStateT :: StateT s1 m a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus, MonadConcat
    , MonadReaderE r, MonadReaderI r, MonadReader r
    , MonadWriterE o, MonadWriterI o, MonadWriter o
    )

mergeState :: (Functor m) => StateT s1 (StateT s2 m) a -> StateT (s1, s2) m a
mergeState aMM = StateT $ \ (s1, s2) -> ff ^$ unStateT (unStateT aMM s1) s2
  where
    ff ((a, s1), s2) = (a, (s1, s2))

splitState :: (Functor m) => StateT (s1, s2) m a -> StateT s1 (StateT s2 m) a
splitState aM = StateT $ \ s1 -> StateT $ \ s2 -> ff ^$ unStateT aM (s1, s2)
  where
    ff (a, (s1, s2)) = ((a, s1), s2)

instance (Functor m, MonadStateE s2 m, Isomorphism s12 (s1, s2)) => MonadStateE s12 (AddStateT s12 s1 m) where
  stateE :: StateT s12 (AddStateT s12 s1 m) ~> AddStateT s12 s1 m
  stateE = 
    AddStateT
    . stateE
    . fmap2 (fmap2 stateE . stateCommute) 
    . splitState
    . mapStateT isoto isofrom
    . fmap2 runAddStateT
instance (Functor m, MonadStateI s2 m, Isomorphism s12 (s1, s2)) => MonadStateI s12 (AddStateT s12 s1 m) where
  stateI :: AddStateT s12 s1 m ~> StateT s12 (AddStateT s12 s1 m)
  stateI = 
    fmap2 AddStateT
    . mapStateT isofrom isoto
    . mergeState
    . fmap2 (stateCommute . fmap2 stateI)
    . stateI
    . runAddStateT
instance (Functor m, MonadState s2 m, Isomorphism s12 (s1, s2)) => MonadState s12 (AddStateT s12 s1 m) where

-- }}}

-- RWST {{{

runRWST :: (Functor m) => r -> s -> RWST r o s m a -> m (a, o, s)
runRWST r0 s0 = ff ^. runStateT s0 . unWriterT . runReaderT r0 . unRWST
  where
    ff ((a, o), s) = (a, o, s)
rwsCommute :: (Monad m, Monoid o1, Monoid o2) => RWST r1 o1 s1 (RWST r2 o2 s2 m) ~> RWST r2 o2 s2 (RWST r1 o1 s1 m)
rwsCommute =
  RWST
  . fmap2 (fmap2 rwsStateCommute . rwsWriterCommute)
  . rwsReaderCommute
  . mmap2 unRWST

deriving instance (Unit m, Monoid o) => Unit (RWST r o s m)
deriving instance (Functor m) => Functor (RWST r o s m)
deriving instance (Monad m, Monoid o) => Product (RWST r o s m)
deriving instance (Monad m, Monoid o) => Applicative (RWST r o s m)
deriving instance (Monad m, Monoid o) => Bind (RWST r o s m)
deriving instance (Monad m, Monoid o) => Monad (RWST r o s m)
instance (Monoid o) => MonadUnit2 (RWST r o s) where
  munit2 = RWST . funit2 . funit2 . funit2
instance (Monoid o) => MonadJoin2 (RWST r o s) where
  mjoin2 =
    RWST
    . fjoin2
    . fmap2 (fmap2 fjoin2 . writerReaderCommute)
    . fmap2 (fmap2 (fmap2 (fmap2 fjoin2 . stateWriterCommute) . stateReaderCommute))
    . unRWST . mmap2 unRWST
instance (Monoid o) => MonadFunctor2 (RWST r o s) where
  mmap2 f = RWST . fmap2 (fmap2 (fmap2 f)) . unRWST

deriving instance (Monad m, Monoid o) => MonadReaderI r (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadReaderE r (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadReader r (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadWriterI o (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadWriterE o (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadWriter o (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadStateI s (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadStateE s (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadState s (RWST r o s m)
instance (Monad m, Monoid o) => MonadRWSI r o s (RWST r o s m) where
  rwsI :: RWST r o s m ~> RWST r o s (RWST r o s m)
  rwsI = rwsCommute . munit2
instance (Monad m, Monoid o) => MonadRWSE r o s (RWST r o s m) where
  rwsE :: RWST r o s (RWST r o s m) ~> RWST r o s m
  rwsE = mjoin2 . rwsCommute
instance (Monad m, Monoid o) => MonadRWS r o s (RWST r o s m) where

deriving instance (MonadZero m, Monoid o) => MonadZero (RWST r o s m)
deriving instance (MonadMaybeI m, Monoid o) => MonadMaybeI (RWST r o s m)
deriving instance (MonadMaybeE m, Monoid o) => MonadMaybeE (RWST r o s m)
deriving instance (MonadMaybe m, Monoid o) => MonadMaybe (RWST r o s m)

-- }}}

-- ListT {{{

listCommute :: (Functor m) => ListT (ListT m) ~> ListT (ListT m)
listCommute = ListT . ListT . transpose ^. unListT . unListT

instance (Unit m) => Unit (ListT m) where
  unit = ListT . unit . single
instance (Functor m) => Functor (ListT m) where
  map f = ListT . f ^^. unListT
instance (Monad m, Functorial Monoid m) => Product (ListT m) where
  (<*>) = mpair
instance (Monad m, Functorial Monoid m) => Applicative (ListT m) where
  (<@>) = mapply
instance (Bind m, Functorial Monoid m) => Bind (ListT m) where
  (>>=) :: forall a b. ListT m a -> (a -> ListT m b) -> ListT m b
  aM >>= k = ListT $ do
    xs <- unListT aM
    unListT $ concat $ k ^$ xs
instance (Monad m, Functorial Monoid m) => Monad (ListT m) where
instance FunctorUnit2 ListT where
  funit2 = ListT .^ unit
instance FunctorJoin2 ListT where
  fjoin2 = ListT . concat ^. unListT . unListT
instance FunctorFunctor2 ListT where
  fmap2 f = ListT . f . unListT

instance (Functorial Monoid m) => Monoid (ListT m a) where
  null = 
    with (functorial :: W (Monoid (m [a]))) $
    ListT null
  xs ++ ys = 
    with (functorial :: W (Monoid (m [a]))) $
    ListT $ unListT xs ++ unListT ys
instance (Functorial Monoid m) => Functorial Monoid (ListT m) where functorial = W
instance (Functorial Monoid m) => MonadZero (ListT m) where
  mzero =  null
instance (Functorial Monoid m) => MonadConcat (ListT m) where
  (<++>) = (++)

-- instance (Monad m, Functorial Monoid m) => MonadListI (ListT m) where
--   listI :: ListT m ~> ListT (ListT m)
--   listI = listCommute . funit2
-- instance (Monad m, Functorial Monoid m) => MonadListE (ListT m) where
--   listE :: ListT (ListT m) ~> ListT m
--   listE = fjoin2 . listCommute
-- instance (Monad m, Functorial Monoid m) => MonadList (ListT m) where

maybeToList :: (Functor m) => MaybeT m a -> ListT m a
maybeToList aM = ListT $ ff ^$ unMaybeT aM
  where
    ff Nothing = []
    ff (Just a) = [a]

-- instance (Monad m, Functorial Monoid m) => MonadMaybeE (ListT m) where
--   maybeE :: MaybeT (ListT m) ~> ListT m
--   maybeE = listE . maybeToList

-- }}}

-- ListSetT {{{

listSetCommute :: (Functor m) => ListSetT (ListSetT m) ~> ListSetT (ListSetT m)
listSetCommute = ListSetT . ListSetT . (ListSet . ListSet ^. transpose . unListSet ^. unListSet) ^. unListSetT . unListSetT

instance (Unit m) => Unit (ListSetT m) where
  unit = ListSetT . unit . ListSet . single
instance (Functor m) => Functor (ListSetT m) where
  map f = ListSetT . f ^^. unListSetT
instance (Monad m, Functorial JoinLattice m) => Product (ListSetT m) where
  (<*>) = mpair
instance (Monad m, Functorial JoinLattice m) => Applicative (ListSetT m) where
  (<@>) = mapply
instance (Bind m, Functorial JoinLattice m) => Bind (ListSetT m) where
  (>>=) :: forall a b. ListSetT m a -> (a -> ListSetT m b) -> ListSetT m b
  aM >>= k = ListSetT $ do
    xs <- unListSetT aM
    unListSetT $ msum $ k ^$ xs
-- PROOF of: monad laws for (ListSetT m) {{{
--
-- ASSUMPTION 1: returnₘ a <+> returnₘ b = returnₘ (a \/ b)
-- [this comes from m being a lattice functor. (1 x + 1 y) = 1 (x + y)]
--
-- * PROOF of: left unit := return x >>= k = k x {{{
--   
--   return x >>= k
--   = [[definition of >>=]]
--   ListSetT $ do { xs <- unListSetT $ return x ; unListSetT $ msums $ map k xs }
--   = [[definition of return]]
--   ListSetT $ do { xs <- unListSetT $ ListSetT $ return [x] ; unListSetT $ msums $ map k xs }
--   = [[ListSetT beta]]
--   ListSetT $ do { xs <- return [x] ; unListSetT $ msums $ map k xs }
--   = [[monad left unit]]
--   ListSetT $ unListSetT $ msums $ map k [x]
--   = [[definition of map]]
--   ListSetT $ unListSetT $ msums $ [k x]
--   = [[definition of msums and <+> unit]]
--   ListSetT $ unListSetT $ k x
--   = [[ListSetT eta]]
--   k x
--   QED }}}
--
-- * PROOF of: right unit := aM >>= return = aM {{{
--
--   aM >>= return
--   = [[definition of >>=]]
--   ListSetT $ { xs <- unListSetT aM ; unListSetT $ msums $ map return xs }
--   = [[induction/expansion on xs]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ msums $ map return [x1,..,xn] }
--   = [[definition of return and map]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ msums $ [ListSetT $ return [x1],..,ListSetT $ return [xn]] }
--   = [[definition of msums]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ ListSetT $ return [x1] <+> .. <+> return [xn] }
--   = [[assumption 1]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ ListSetT $ return [x1,..,xn] }
--   = [[ListSetT beta]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; return [x1,..,xn] }
--   = [[monad right unit]]
--   ListSetT $ unListSetT aM
--   = [[ListSetT eta]]
--   aM
--   QED }}}
--
-- * PROOF of: associativity := (aM >>= k1) >>= k2 = { x <- aM ; k1 x >>= k2 } {{{
--
--   (aM >>= k1) >>= k2
--   = [[definition of >>=]]
--   ListSetT $ { xs <- unListSetT $ ListSetT $ { xs' <- unListSetT aM ; unListSetT $ msums $ map k1 xs' } ; unListSetT $ msums $ map k xs }
--   = [[ListSetT beta]]
--   ListSetT $ { xs <- { xs' <- unListSetT aM ; unListSetT $ msums $ map k1 xs' } ; unListSetT $ msums $ map k xs }
--   = [[monad associativity]]
--   ListSetT $ { xs' <- unListSetT aM ; xs <- unListSetT $ msums $ map k1 xs' ; unListSetT $ msums $ map k xs }
--   =
--   LHS
--
--   { x <- aM ; k1 x >>= k2 }
--   = [[definition of >>=]]
--   ListSetT $ { xs' <- unListSetT aM ; unListSetT $ msums $ map (\ x -> ListSetT $ { xs <- unListSetT (k1 x) ; unListSetT $ msums $ map k2 xs }) xs' }
--   = [[induction/expansion on xs']]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ msums $ map (\ x -> ListSetT $ { xs <- unListSetT (k1 x) ; unListSetT $ msums $ map k2 xs }) [x1,..,xn] }
--   = [[definition of map]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ msums $ [ListSetT $ { xs <- unListSetT (k1 x1) ; unListSetT $ msums $ map k2 xs },..,ListSetT $ { xs <- unListSetT (k1 xn) ; runList $ msums $ map k2 xs}] }
--   = [[definition of msum]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; unListSetT $ ListSetT { xs <- unListSetT (k1 x1) ; unListSetT $ msums $ map k2 xs } <+> .. <+> ListSetT { xs <- unListSetT (k1 xn) ; unListSetT $ msums $ map k2 xs } }
--   = [[ListSetT beta and definition of <+> for ListSetT]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; { xs <- unListSetT (k1 x1) ; unListSetT $ msums $ map k2 xs } <+> .. <+> { xs <- unListSetT (k1 xn) ; unListSetT $ msums $ map k2 xs } }
--   = [[<+> distribute with >>=]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; xs <- (unListSetT (k1 x1) <+> .. <+> unListSetT (k1 xn)) ;  unListSetT $ msums $ map k2 xs }
--   = [[definition of msums and map]]
--   ListSetT $ { [x1,..,xn] <- unListSetT aM ; xs <- unListSetT $ msums $ map k1 [x1,..,xn] ; unListSetT $ msums $ map k2 xs }
--   = [[collapsing [x1,..,xn]]]
--   ListSetT $ { xs' <- unListSetT aM ; xs <- unListSetT $ msums $ map k1 xs' ; unListSetT $ msums $ map k xs }
--   =
--   RHS
--
--   LHS = RHS
--   QED }}}
--
-- }}}
instance (Monad m, Functorial JoinLattice m) => Monad (ListSetT m) where
instance FunctorUnit2 ListSetT where
  funit2 = ListSetT .^ unit
instance FunctorJoin2 ListSetT where
  fjoin2 = ListSetT . concat ^. unListSetT . unListSetT
instance FunctorFunctor2 ListSetT where
  fmap2 f = ListSetT . f . unListSetT

instance (Functorial JoinLattice m) => MonadZero (ListSetT m) where
  mzero :: forall a. ListSetT m a
  mzero = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT bot
instance (Functorial JoinLattice m) => MonadPlus (ListSetT m) where
  (<+>) :: forall a. ListSetT m a -> ListSetT m a -> ListSetT m a
  aM1 <+> aM2 = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT $ unListSetT aM1 \/ unListSetT aM2

-- instance (Monad m, Functorial JoinLattice m) => MonadListSetI (ListSetT m) where
--   listSetI :: ListSetT m ~> ListSetT (ListSetT m)
--   listSetI = listSetCommute . funit2
-- instance (Monad m, Functorial JoinLattice m) => MonadListSetE (ListSetT m) where
--   listSetE :: ListSetT (ListSetT m) ~> ListSetT m
--   listSetE = fjoin2 . listSetCommute
-- instance (Monad m, Functorial JoinLattice m) => MonadListSet (ListSetT m) where

-- }}}

-- SetT {{{

setCommute :: (Functor m) => SetT (SetT m) ~> SetT (SetT m)
setCommute = SetT . SetT . setTranspose ^. unSetT . unSetT

instance (Functor m, Product m) => Product (SetT m) where
  (<*>) :: forall a b. SetT m a -> SetT m b -> SetT m (a, b)
  aM1 <*> aM2 = SetT $ uncurry ff ^$ unSetT aM1 <*> unSetT aM2
    where
      ff :: Set a -> Set b -> Set (a, b)
      ff s1 s2 = 
        learnSet s1 empty $
        learnSet s2 empty $
        toSet $ fromSet s1 <*> fromSet s2
instance (Functorial JoinLattice m, Bind m) => Bind (SetT m) where
  aM >>= k = SetT $ do
    aC <- unSetT aM
    unSetT $ msum $ k ^$ fromSet aC
instance (Functorial JoinLattice m) => MonadZero (SetT m) where
  mzero :: forall a. SetT m a
  mzero = 
    with (functorial :: W (JoinLattice (m (Set a)))) $
    SetT bot
instance (Functorial JoinLattice m) => MonadPlus (SetT m) where
  (<+>) :: forall a. SetT m a -> SetT m a -> SetT m a
  aM1 <+> aM2 =
    with (functorial :: W (JoinLattice (m (Set a)))) $
    SetT $ unSetT aM1 \/ unSetT aM2

-- }}}

-- KonT {{{

evalKonT :: (Unit m) => KonT r m r -> m r
evalKonT aM = unKonT aM unit

type Kon r = KonT r ID
runKon :: Kon r a -> (a -> r) -> r
runKon aM f = unID $ unKonT aM (ID . f)
evalKon :: Kon r r -> r
evalKon aM = runKon aM id

instance (Unit m) => Unit (KonT r m) where
  unit a = KonT $ \ k -> k a
instance (Unit m) => Applicative (KonT r m) where
  (<@>) = mapply
instance (Unit m) => Product (KonT r m) where
  (<*>) = mpair
instance (Unit m) => Functor (KonT r m) where
  map = mmap
instance (Unit m) => Bind (KonT r m) where
  (>>=) :: KonT r m a -> (a -> KonT r m b) -> KonT r m b
  aM >>= kM = KonT $ \ (k :: b -> m r) -> unKonT aM $ \ a -> unKonT (kM a) k
instance (Unit m) => Monad (KonT r m) where
instance MonadIsoFunctor2 (KonT r) where
  misoMap2 :: (Monad m, Monad n) => m ~> n -> n ~> m -> KonT r m ~> KonT r n
  misoMap2 to from aM = KonT $ \ (k :: a -> n r) -> to $ unKonT aM $ \ a -> from $ k a

instance (Monad m) => MonadKonI r (KonT r m) where
  konI :: KonT r m ~> KonT r (KonT r m)
  konI aM = KonT $ \ (k1 :: a -> KonT r m r) -> KonT $ \ (k2 :: r -> m r) ->
    k2 *$ unKonT aM $ \ a -> unKonT (k1 a) return
instance (Monad m) => MonadKonE r (KonT r m) where
  konE :: KonT r (KonT r m) ~> KonT r m
  konE aMM = KonT $ \ (k :: a -> m r) -> 
    let aM :: KonT r m r
        aM = unKonT aMM $ \ a -> KonT $ \ (k' :: r -> m r) -> k' *$ k a
    in unKonT aM return
instance (Monad m) => MonadKon r (KonT r m) where

-- }}}

-- OpaqueKonT {{{

runOpaqueKonTWith :: k r m a -> OpaqueKonT k r m a -> m r
runOpaqueKonTWith = flip unOpaqueKonT
makeMetaKonT :: (Morphism3 (k r) (KFun r)) => ((a -> m r) -> m r) -> OpaqueKonT k r m a
makeMetaKonT nk = OpaqueKonT $ \ (k :: k r m a) -> nk $ unKFun $ morph3 k
runMetaKonT :: (Morphism3 (KFun r) (k r)) => OpaqueKonT k r m a -> (a -> m r) -> m r
runMetaKonT aM k = unOpaqueKonT aM $ morph3 $ KFun k
runMetaKonTWith :: (Morphism3 (KFun r) (k r)) => (a -> m r) -> OpaqueKonT k r m a -> m r
runMetaKonTWith = flip runMetaKonT
evalOpaqueKonT :: (Unit m, Morphism3 (KFun r) (k r)) => OpaqueKonT k r m r -> m r
evalOpaqueKonT aM = runMetaKonT aM unit

type OpaqueKon k r = OpaqueKonT k r ID

makeOpaqueKon :: (k r ID a -> r) -> OpaqueKon k r a
makeOpaqueKon nk = OpaqueKonT $ ID . nk
makeMetaKon :: (Morphism3 (k r) (KFun r)) => ((a -> r) -> r) -> OpaqueKon k r a
makeMetaKon nk = makeOpaqueKon $ \ (k :: k r ID a) -> nk $ (.) unID . unKFun $ morph3 k
runOpaqueKon :: OpaqueKon k r a -> k r ID a -> r
runOpaqueKon = unID .: unOpaqueKonT
runMetaKon :: (Morphism3 (KFun r) (k r)) => OpaqueKon k r a -> (a -> r) -> r
runMetaKon aM k = runOpaqueKon aM $ morph3 $ KFun $ ID . k
evalOpaqueKon :: (Morphism3 (KFun r) (k r)) => OpaqueKon k r r -> r
evalOpaqueKon aM = runMetaKon aM id

metaKonT :: (Morphism3 (KFun r) (k r)) => OpaqueKonT k r m ~> KonT r m
metaKonT aM = KonT $ \ (k :: a -> m r) -> runMetaKonT aM k

opaqueKonT :: (Morphism3 (k r) (KFun r)) => KonT r m ~> OpaqueKonT k r m
opaqueKonT aM = makeMetaKonT $ \ (k :: a -> m r) -> unKonT aM k

instance (Monad m, Morphism3 (k r) (KFun r)) => Unit (OpaqueKonT k r m) where
  unit :: a -> OpaqueKonT k r m a
  unit = opaqueKonT . unit
instance (Monad m, Isomorphism3 (KFun r) (k r)) => Functor (OpaqueKonT k r m) where
  map = mmap
instance (Monad m, Isomorphism3 (KFun r) (k r)) => Applicative (OpaqueKonT k r m) where
  (<@>) = mapply
instance (Monad m, Isomorphism3 (KFun r) (k r)) => Product (OpaqueKonT k r m) where
  (<*>) = mpair
instance (Monad m, Isomorphism3 (KFun r) (k r)) => Bind (OpaqueKonT k r m) where
  (>>=) :: OpaqueKonT k r m a -> (a -> OpaqueKonT k r m b) -> OpaqueKonT k r m b
  aM >>= kM = OpaqueKonT $ \ (k :: k r m a) -> runMetaKonT aM $ \ a -> unOpaqueKonT (kM a) k
instance (Monad m, Isomorphism3 (KFun r) (k r)) => Monad (OpaqueKonT k r m) where
instance (Isomorphism3 (k r) (KFun r)) => MonadIsoFunctor2 (OpaqueKonT k r) where
  misoMap2 :: (Monad m, Monad n) => m ~> n -> n ~> m -> OpaqueKonT k r m ~> OpaqueKonT k r n
  misoMap2 to from = opaqueKonT . misoMap2 to from . metaKonT

class Balloon k r | k -> r where
  inflate :: (Monad m) => k r m ~> k r (OpaqueKonT k r m)
  deflate :: (Monad m) => k r (OpaqueKonT k r m) ~> k r m
instance (Monad m, Isomorphism3 (KFun r) (k r), Balloon k r) => MonadOpaqueKonI k r (OpaqueKonT k r m) where
  withOpaqueC :: k r (OpaqueKonT k r m) a -> OpaqueKonT k r m a -> OpaqueKonT k r m r
  withOpaqueC k1 aM = makeMetaKonT $ \ (k2 :: r -> m r) -> k2 *$ unOpaqueKonT aM $ deflate k1
instance (Monad m, Isomorphism3 (KFun r) (k r), Balloon k r) => MonadOpaqueKonE k r (OpaqueKonT k r m) where
  callOpaqueCC :: (k r (OpaqueKonT k r m) a -> OpaqueKonT k r m r) -> OpaqueKonT k r m a
  callOpaqueCC kk = OpaqueKonT $ \ (k :: k r m a ) -> runMetaKonTWith return $ kk $ inflate k
instance (Monad m, Isomorphism3 (KFun r) (k r), Balloon k r) => MonadOpaqueKon k r (OpaqueKonT k r m) where

instance (Monad m, Isomorphism3 (KFun r) (k r)) => MonadKonI r (OpaqueKonT k r m) where
  konI :: OpaqueKonT k r m ~> KonT r (OpaqueKonT k r m)
  konI aM = KonT $ \ (k1 :: a -> OpaqueKonT k r m r) -> makeMetaKonT $ \ (k2 :: r -> m r) ->
    k2 *$ runMetaKonT aM $ \ a -> runMetaKonT (k1 a) return
instance (Monad m, Isomorphism3 (KFun r) (k r)) => MonadKonE r (OpaqueKonT k r m) where
  konE :: KonT r (OpaqueKonT k r m) ~> OpaqueKonT k r m
  konE aMM = makeMetaKonT $ \ (k :: a -> m r) ->
    runMetaKonTWith return $ unKonT aMM $ \ a -> makeMetaKonT $ \ (k' :: r -> m r) -> k' *$ k a
instance (Monad m, Isomorphism3 (KFun r) (k r)) => MonadKon r (OpaqueKonT k r m) where

-- }}}

----------------------
-- Monads Commuting --
----------------------

-- Maybe // * --

-- Maybe // Reader // FULL COMMUTE {{{

maybeReaderCommute :: (Monad m) => MaybeT (ReaderT r m) ~> ReaderT r (MaybeT m)
maybeReaderCommute aMRM = ReaderT $ \ r -> MaybeT $ runReaderT r $ unMaybeT aMRM

readerMaybeCommute :: (Monad m) => ReaderT r (MaybeT m) ~> MaybeT (ReaderT r m)
readerMaybeCommute aRMM = MaybeT $ ReaderT $ \ r -> unMaybeT $ runReaderT r aRMM

instance (MonadReaderI r m) => MonadReaderI r (MaybeT m) where
  readerI :: MaybeT m ~> ReaderT r (MaybeT m)
  readerI = maybeReaderCommute . fmap2 readerI
instance (MonadReaderE r m) => MonadReaderE r (MaybeT m) where
  readerE :: ReaderT r (MaybeT m) ~> MaybeT m
  readerE = fmap2 readerE . readerMaybeCommute
instance (MonadReader r m) => MonadReader r (MaybeT m) where

instance (MonadMaybeI m) => MonadMaybeI (ReaderT r m) where
  maybeI :: ReaderT r m ~> MaybeT (ReaderT r m)
  maybeI = readerMaybeCommute . fmap2 maybeI
instance (MonadMaybeE m) => MonadMaybeE (ReaderT r m) where
  maybeE :: MaybeT (ReaderT r m) ~> ReaderT r m
  maybeE = fmap2 maybeE . maybeReaderCommute
instance (MonadMaybe m) => MonadMaybe (ReaderT r m) where

-- }}}

-- Maybe // Writer {{{

writerMaybeCommute :: (Monoid w, Monad m) => WriterT w (MaybeT m) ~> MaybeT (WriterT w m)
writerMaybeCommute aRMM = MaybeT $ WriterT $ do
  awM <- unMaybeT $ unWriterT aRMM
  return $ case awM of
    Nothing -> (Nothing, null)
    Just (a, w) -> (Just a, w)

maybeWriterCommute :: (Monad m) => MaybeT (WriterT w m) ~> WriterT w (MaybeT m)
maybeWriterCommute aMRM = WriterT $ MaybeT $ do
  (aM, w) <- unWriterT $ unMaybeT aMRM
  return $ case aM of
    Nothing -> Nothing
    Just a -> Just (a, w)

instance (Monoid w, MonadWriter w m) => MonadWriterI w (MaybeT m) where
  writerI :: MaybeT m ~> WriterT w (MaybeT m)
  writerI = maybeWriterCommute . fmap2 writerI
instance (Monoid w, MonadWriter w m) => MonadWriterE w (MaybeT m) where
  writerE :: WriterT w (MaybeT m) ~> MaybeT m
  writerE = fmap2 writerE . writerMaybeCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (MaybeT m) where

instance (Monoid w, MonadMaybeI m) => MonadMaybeI (WriterT w m) where
  maybeI :: WriterT w m ~> MaybeT (WriterT w m)
  maybeI = writerMaybeCommute . fmap2 maybeI
instance (Monoid w, MonadMaybeE m) => MonadMaybeE (WriterT w m) where
  maybeE :: MaybeT (WriterT w m) ~> WriterT w m
  maybeE = fmap2 maybeE . maybeWriterCommute
instance (Monoid w, MonadMaybe m) => MonadMaybe (WriterT w m) where

-- }}}

-- Maybe // State {{{

maybeStateCommute :: (Functor m) => MaybeT (StateT s m) ~> StateT s (MaybeT m)
maybeStateCommute aMSM = StateT $ \ s1 -> MaybeT $ ff ^$ runStateT s1 $ unMaybeT aMSM
  where
    ff (Nothing, _) = Nothing
    ff (Just a, s2) = Just (a, s2)

stateMaybeCommute :: (Functor m) => StateT s (MaybeT m) ~> MaybeT (StateT s m)
stateMaybeCommute aSMM = MaybeT $ StateT $ \ s1 -> ff s1 ^$ unMaybeT $ runStateT s1 aSMM
  where
    ff s1 Nothing = (Nothing, s1)
    ff _ (Just (a, s2)) = (Just a, s2)

instance (Functor m, MonadStateI s m) => MonadStateI s (MaybeT m) where
  stateI :: MaybeT m ~> StateT s (MaybeT m)
  stateI = maybeStateCommute . fmap2 stateI
instance (Functor m, MonadStateE s m) => MonadStateE s (MaybeT m) where
  stateE :: StateT s (MaybeT m) ~> MaybeT m
  stateE = fmap2 stateE . stateMaybeCommute
instance (Functor m, MonadState s m) => MonadState s (MaybeT m) where

instance (MonadMaybeI m) => MonadMaybeI (StateT s m) where
  maybeI :: StateT s m ~> MaybeT (StateT s m)
  maybeI = stateMaybeCommute . fmap2 maybeI
instance (MonadMaybeE m) => MonadMaybeE (StateT s m) where
  maybeE :: MaybeT (StateT s m) ~> StateT s m
  maybeE = fmap2 maybeE . maybeStateCommute
instance (MonadMaybe m) => MonadMaybe (StateT s m) where

-- }}}

-- Error // * --

-- Error // Reader {{{

errorReaderCommute :: (Monad m) => ErrorT e (ReaderT r m) ~> ReaderT r (ErrorT e m)
errorReaderCommute aMRM = ReaderT $ \ r -> ErrorT $ runReaderT r $ unErrorT aMRM

readerErrorCommute :: (Monad m) => ReaderT r (ErrorT e m) ~> ErrorT e (ReaderT r m)
readerErrorCommute aRMM = ErrorT $ ReaderT $ \ r -> unErrorT $ runReaderT r aRMM

instance (MonadReaderI r m) => MonadReaderI r (ErrorT e m) where
  readerI :: ErrorT e m ~> ReaderT r (ErrorT e m)
  readerI = errorReaderCommute . fmap2 readerI
instance (MonadReaderE r m) => MonadReaderE r (ErrorT e m) where
  readerE :: ReaderT r (ErrorT e m) ~> ErrorT e m
  readerE = fmap2 readerE . readerErrorCommute
instance (MonadReader r m) => MonadReader r (ErrorT e m) where

instance (MonadErrorI e m) => MonadErrorI e (ReaderT r m) where
  errorI :: ReaderT r m ~> ErrorT e (ReaderT r m)
  errorI = readerErrorCommute . fmap2 errorI
instance (MonadErrorE e m) => MonadErrorE e (ReaderT r m) where
  errorE :: ErrorT e (ReaderT r m) ~> ReaderT r m
  errorE = fmap2 errorE . errorReaderCommute
instance (MonadError e m) => MonadError e (ReaderT r m) where

-- }}}

-- Error // State {{{

errorStateCommute :: (Functor m) => ErrorT e (StateT s m) ~> StateT s (ErrorT e m)
errorStateCommute aMRM = StateT $ \ s -> ErrorT $ ff ^$ runStateT s $ unErrorT aMRM
  where
    ff :: (e :+: a, s) -> e :+: (a, s)
    ff (Inl e, _) = Inl e
    ff (Inr a, s) = Inr $ (a, s)

stateErrorCommute :: (Functor m) => StateT s (ErrorT e m) ~> ErrorT e (StateT s m)
stateErrorCommute aRMM = ErrorT $ StateT $ \ s -> ff s ^$ unErrorT $ runStateT s aRMM
  where
    ff :: s -> e :+: (a, s) -> (e :+: a, s)
    ff s (Inl e) = (Inl e, s)
    ff _ (Inr (a, s)) = (Inr a, s)

instance (Functor m, MonadStateI s m) => MonadStateI s (ErrorT e m) where
  stateI :: ErrorT e m ~> StateT s (ErrorT e m)
  stateI = errorStateCommute . fmap2 stateI
instance (Functor m, MonadStateE s m) => MonadStateE s (ErrorT e m) where
  stateE :: StateT s (ErrorT e m) ~> ErrorT e m
  stateE = fmap2 stateE . stateErrorCommute
instance (Functor m, MonadState s m) => MonadState s (ErrorT e m) where

instance (MonadErrorI e m) => MonadErrorI e (StateT s m) where
  errorI :: StateT s m ~> ErrorT e (StateT s m)
  errorI = stateErrorCommute . fmap2 errorI
instance (MonadErrorE e m) => MonadErrorE e (StateT s m) where
  errorE :: ErrorT e (StateT s m) ~> StateT s m
  errorE = fmap2 errorE . errorStateCommute
instance (MonadError e m) => MonadError e (StateT s m) where

-- }}}

-- Reader // * --

-- Reader // Writer // FULL COMMUTE {{{

readerWriterCommute :: ReaderT r (WriterT w m) ~> WriterT w (ReaderT r m)
readerWriterCommute aRWM = WriterT $ ReaderT $ \ r -> unWriterT $ runReaderT r aRWM

writerReaderCommute :: WriterT w (ReaderT r m) ~> ReaderT r (WriterT w m)
writerReaderCommute aWRM = ReaderT $ \ r -> WriterT $ runReaderT r $ unWriterT aWRM

instance (Monoid w, MonadWriterI w m) => MonadWriterI w (ReaderT r m) where
  writerI :: ReaderT r m ~> WriterT w (ReaderT r m)
  writerI = readerWriterCommute . fmap2 writerI
instance (Monoid w, MonadWriterE w m) => MonadWriterE w (ReaderT r m) where
  writerE :: WriterT w (ReaderT r m) ~> ReaderT r m
  writerE = fmap2 writerE . writerReaderCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (ReaderT r m) where

instance (Monoid w, MonadReaderI r m) => MonadReaderI r (WriterT w m) where
  readerI :: WriterT w m ~> ReaderT r (WriterT w m)
  readerI = writerReaderCommute . fmap2 readerI
instance (Monoid w, MonadReaderE r m) => MonadReaderE r (WriterT w m) where
  readerE :: ReaderT r (WriterT w m) ~> WriterT w m
  readerE = fmap2 readerE . readerWriterCommute
instance (Monoid w, MonadReader r m) => MonadReader r (WriterT w m) where

-- }}}

-- Reader // State // FULL COMMUTE {{{

readerStateCommute :: (Functor m) => ReaderT r (StateT s m) ~> StateT s (ReaderT r m)
readerStateCommute aRSM = StateT $ \ s -> ReaderT $ \ r ->
  runStateT s $ runReaderT r aRSM

stateReaderCommute :: (Functor m) => StateT s (ReaderT r m) ~> ReaderT r (StateT s m)
stateReaderCommute aSRM = ReaderT $ \ r -> StateT $ \ s -> 
  runReaderT r $ runStateT s aSRM

instance (Functor m, MonadStateI s m) => MonadStateI s (ReaderT r m) where
  stateI :: ReaderT r m ~> StateT s (ReaderT r m)
  stateI = readerStateCommute . fmap2 stateI
instance (Functor m, MonadStateE s m) => MonadStateE s (ReaderT r m) where
  stateE :: StateT s (ReaderT r m) ~> ReaderT r m
  stateE = fmap2 stateE . stateReaderCommute
instance (Functor m, MonadState s m) => MonadState s (ReaderT r m) where

instance (MonadReaderI r m) => MonadReaderI r (StateT s m) where
  readerI :: StateT s m ~> ReaderT r (StateT s m)
  readerI = stateReaderCommute . fmap2 readerI
instance (MonadReaderE r m) => MonadReaderE r (StateT s m) where
  readerE :: ReaderT r (StateT s m) ~> StateT s m
  readerE = fmap2 readerE . readerStateCommute
instance (MonadReader r m) => MonadReader r (StateT s m) where

-- }}}

-- Reader // RWS {{{

readerRWSCommute :: (Monad m, Monoid o) => ReaderT r1 (RWST r2 o s m) ~> RWST r2 o s (ReaderT r1 m)
readerRWSCommute =
    RWST
  . fmap2 
    ( fmap2 readerStateCommute
    . readerWriterCommute
    )
  . readerCommute
  . fmap2 unRWST

rwsReaderCommute :: (Monad m, Monoid o) => RWST r1 o s (ReaderT r2 m) ~> ReaderT r2 (RWST r1 o s m)
rwsReaderCommute = 
    fmap2 RWST
  . readerCommute
  . fmap2 
    ( writerReaderCommute
    . fmap2 stateReaderCommute
    )
  . unRWST
       
-- }}}

-- Writer // * --

-- Writer // State // FULL COMMUTE {{{

writerStateCommute :: (Functor m) => WriterT w (StateT s m) ~> StateT s (WriterT w m)
writerStateCommute aRMM = StateT $ \ s1 -> WriterT $ ff ^$ runStateT s1 $ unWriterT aRMM
  where
    ff ((a, w), s) = ((a, s), w)

stateWriterCommute :: (Functor m) => StateT s (WriterT w m) ~> WriterT w (StateT s m)
stateWriterCommute aMRM = WriterT $ StateT $ ff ^. unWriterT . unStateT aMRM
  where
    ff ((a, s), w) = ((a, w), s)

instance (Functor m, Monoid w, MonadStateI s m) => MonadStateI s (WriterT w m) where
  stateI :: WriterT w m ~> StateT s (WriterT w m)
  stateI = writerStateCommute . fmap2 stateI
instance (Functor m, Monoid w, MonadStateE s m) => MonadStateE s (WriterT w m) where
  stateE :: StateT s (WriterT w m) ~> WriterT w m
  stateE = fmap2 stateE . stateWriterCommute
instance (Functor m, Monoid w, MonadState s m) => MonadState s (WriterT w m) where

instance (Monoid w, MonadWriter w m) => MonadWriterI w (StateT s m) where
  writerI :: StateT s m ~> WriterT w (StateT s m)
  writerI = stateWriterCommute . fmap2 writerI
instance (Monoid w, MonadWriter w m) => MonadWriterE w (StateT s m) where
  writerE :: WriterT w (StateT s m) ~> StateT s m
  writerE = fmap2 writerE . writerStateCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (StateT s m) where

-- }}}

-- Writer // RWS {{{

writerRWSCommute :: (Monad m, Monoid o1, Monoid o2) => WriterT o1 (RWST r o2 s m) ~> RWST r o2 s (WriterT o1 m)
writerRWSCommute =
    RWST
  . fmap2 
    ( fmap2 writerStateCommute
    . writerCommute
    )
  . writerReaderCommute
  . fmap2 unRWST

rwsWriterCommute :: (Monad m, Monoid o1, Monoid o2) => RWST r o1 s (WriterT o2 m) ~> WriterT o2 (RWST r o1 s m)
rwsWriterCommute =
    fmap2 RWST
  . readerWriterCommute
  . fmap2 
    ( writerCommute
    . fmap2 stateWriterCommute
    )
  . unRWST

-- }}}

-- State // * --

-- State // RWS {{{

stateRWSCommute :: (Monad m, Monoid o) => StateT s1 (RWST r o s2 m) ~> RWST r o s2 (StateT s1 m)
stateRWSCommute =
    RWST
  . fmap2 
    ( fmap2 stateCommute
    . stateWriterCommute
    )
  . stateReaderCommute
  . fmap2 unRWST

rwsStateCommute :: (Monad m, Monoid o) => RWST r o s1 (StateT s2 m) ~> StateT s2 (RWST r o s1 m)
rwsStateCommute =
    fmap2 RWST
  . readerStateCommute
  . fmap2 
    ( writerStateCommute
    . fmap2 stateCommute
    )
  . unRWST

-- }}}

-- State // List {{{

-- (s -> m [a, s]) -> (s -> m ([a], s))

stateListCommute :: (Functor m, Monoid s) => StateT s (ListT m) ~> ListT (StateT s m)
stateListCommute aMM = ListT $ StateT $ \ s -> ff ^$ unListT $ runStateT s aMM
  where
    ff asL = (fst ^$ asL, concat $ snd ^$ asL)

listStateCommute :: (Functor m) => ListT (StateT s m) ~> StateT s (ListT m)
listStateCommute aMM = StateT $ \ s -> ListT $ ff ^$ runStateT s $ unListT aMM
  where
    ff (xs, s) = (,s) ^$ xs

-- instance (MonadListI m, Functorial Monoid m, Monoid s) => MonadListI (StateT s m) where
--   listI :: StateT s m ~> ListT (StateT s m)
--   listI = stateListCommute . fmap2 listI
-- instance (MonadListE m, Functorial Monoid m) => MonadListE (StateT s m) where
--   listE :: ListT (StateT s m) ~> StateT s m
--   listE = fmap2 listE . listStateCommute
-- instance (MonadList m, Functorial Monoid m, Monoid s) => MonadList (StateT s m) where

instance (Functor m, MonadStateI s m, Functorial Monoid m) => MonadStateI s (ListT m) where
  stateI :: ListT m ~> StateT s (ListT m)
  stateI = listStateCommute . fmap2 stateI
instance (Functor m, MonadStateE s m, Functorial Monoid m, Monoid s) => MonadStateE s (ListT m) where
  stateE :: StateT s (ListT m) ~> ListT m
  stateE = fmap2 stateE . stateListCommute
instance (Functor m, MonadState s m, Functorial Monoid m, Monoid s) => MonadState s (ListT m) where

-- }}}

-- State // ListSet {{{

stateListSetCommute :: (Functor m, JoinLattice s) => StateT s (ListSetT m) ~> ListSetT (StateT s m)
stateListSetCommute aMM = ListSetT $ StateT $ \ s -> ff ^$ unListSetT $ runStateT s aMM
  where
    ff asL = (fst ^$ asL, joins $ snd ^$ asL)

listSetStateCommute :: (Functor m) => ListSetT (StateT s m) ~> StateT s (ListSetT m)
listSetStateCommute aMM = StateT $ \ s -> ListSetT $ ff ^$ runStateT s $ unListSetT aMM
  where
    ff (xs, s) = (,s) ^$ xs

-- instance (MonadListSetI m, Functorial JoinLattice m, JoinLattice s) => MonadListSetI (StateT s m) where
--   listSetI :: StateT s m ~> ListSetT (StateT s m)
--   listSetI = stateListSetCommute . fmap2 listSetI
-- instance (MonadListSetE m, Functorial JoinLattice m) => MonadListSetE (StateT s m) where
--   listSetE :: ListSetT (StateT s m) ~> StateT s m
--   listSetE = fmap2 listSetE . listSetStateCommute
-- instance (MonadListSet m, Functorial JoinLattice m, JoinLattice s) => MonadListSet (StateT s m) where

instance (Functor m, MonadStateI s m, Functorial JoinLattice m) => MonadStateI s (ListSetT m) where
  stateI :: ListSetT m ~> StateT s (ListSetT m)
  stateI = listSetStateCommute . fmap2 stateI
instance (Functor m, MonadStateE s m, Functorial JoinLattice m, JoinLattice s) => MonadStateE s (ListSetT m) where
  stateE :: StateT s (ListSetT m) ~> ListSetT m
  stateE = fmap2 stateE . stateListSetCommute
instance (Functor m, MonadState s m, Functorial JoinLattice m, JoinLattice s) => MonadState s (ListSetT m) where

-- }}}

-- State // Kon {{{

stateKonCommute :: StateT s (KonT (r, s) m) ~> KonT r (StateT s m)
stateKonCommute aSK = KonT $ \ (k :: a -> StateT s m r) -> StateT $ \ s ->
  unKonT (runStateT s aSK) $ \ (a, s') -> runStateT s' $ k a

konStateCommute :: KonT r (StateT s m) ~> StateT s (KonT (r, s) m)
konStateCommute aKS = StateT $ \ s -> KonT $ \ (k :: (a, s) -> m (r, s)) ->
  runStateT s $ unKonT aKS $ \ a -> StateT $ \ s' -> k (a, s')

instance (Monad m, MonadState s m) => MonadStateI s (KonT r m) where
  stateI :: KonT r m ~> StateT s (KonT r m)
  stateI =
    fmap2 (misoMap2 stateE stateI)
    . fmap2 stateKonCommute
    . stateI
    . konStateCommute
    . misoMap2 stateI (stateE :: StateT s m ~> m)
instance (Monad m, MonadState s m) => MonadStateE s (KonT r m) where
  stateE :: StateT s (KonT r m) ~> KonT r m
  stateE =
    misoMap2 stateE stateI
    . stateKonCommute
    . stateE
    . fmap2 konStateCommute
    . fmap2 (misoMap2 stateI (stateE :: StateT s m ~> m))

-- }}}

-- State // OpaqueKon {{{

instance (Monad m, MonadState s m, Isomorphism3 (KFun r) (k r)) => MonadStateI s (OpaqueKonT k r m) where
  stateI :: OpaqueKonT k r m ~> StateT s (OpaqueKonT k r m)
  stateI =
    fmap2 opaqueKonT
    . stateI
    . metaKonT
instance (Monad m, MonadState s m, Isomorphism3 (KFun r) (k r)) => MonadStateE s (OpaqueKonT k r m) where
  stateE :: StateT s (OpaqueKonT k r m) ~> OpaqueKonT k r m
  stateE =
    opaqueKonT
    . stateE
    . fmap2 metaKonT
instance (Monad m, MonadState s m, Isomorphism3 (KFun r) (k r)) => MonadState s (OpaqueKonT k r m) where

-- }}}
