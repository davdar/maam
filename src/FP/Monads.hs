module FP.Monads where

import FP.Core

---------------------
-- Monadic Effects --
---------------------

-- ID {{{

newtype ID a = ID { runID :: a }
  deriving
  ( Eq, Ord
  , PartialOrder
  , HasBot
  , Monoid
  , JoinLattice
  )

instance Unit ID where
  unit = ID
instance CUnit Universal ID where
  cunit = unit
instance Functor ID where
  map f = ID . f . runID
instance FunctorM ID where
  mapM f = map ID . f . runID
instance CFunctor Universal ID where
  cmap = map
instance CFunctorM Universal ID where
  cmapM = mapM
instance Product ID where
  aM <*> bM = ID $ (runID aM, runID bM)
instance Applicative ID where
  fM <@> aM = ID $ runID fM $ runID aM
instance Bind ID where
  aM >>= k = k $ runID aM
instance Monad ID where
instance Functorial HasBot ID where
  functorial = W
instance Functorial JoinLattice ID where
  functorial = W
instance Functorial Monoid ID where
  functorial = W

newtype IDT m a = IDT { runIDT :: m a }

-- }}}

-- MaybeT {{{

maybeCommute :: (Functor m) => MaybeT (MaybeT m) ~> MaybeT (MaybeT m)
maybeCommute aMM = MaybeT $ MaybeT $ ff ^$ runMaybeT $ runMaybeT aMM
  where
    ff Nothing = Just Nothing
    ff (Just Nothing) = Nothing
    ff (Just (Just a)) = Just (Just a)
  
instance (Unit m) => Unit (MaybeT m) where
  unit = MaybeT . unit . Just
instance (Functor m) => Functor (MaybeT m) where
  map f = MaybeT . f ^^. runMaybeT
instance (Functor m, Product m) => Product (MaybeT m) where
  aM1 <*> aM2 = MaybeT $ uncurry ff ^$ runMaybeT aM1 <*> runMaybeT aM2
    where
      ff Nothing _ = Nothing
      ff _ Nothing = Nothing
      ff (Just a1) (Just a2) = Just (a1, a2)
instance (Functor m, Applicative m) => Applicative (MaybeT m) where
  fM <@> aM = MaybeT $ ff ^@ runMaybeT fM <$> runMaybeT aM
    where
      ff Nothing _ = Nothing
      ff _ Nothing = Nothing
      ff (Just f) (Just a) = Just $ f a
instance (Monad m) => Bind (MaybeT m) where
  aM >>= k = MaybeT $ do
    aM' <- runMaybeT aM
    case aM' of
      Nothing -> return Nothing
      Just a -> runMaybeT $ k a
instance (Monad m) => Monad (MaybeT m) where

instance FunctorUnit MaybeT where
  ftUnit = MaybeT .^ Just
instance FunctorJoin MaybeT where
  ftJoin = MaybeT . ff ^. runMaybeT . runMaybeT
    where
      ff Nothing = Nothing
      ff (Just aM) = aM
instance MonadFunctor MaybeT where
  mtMap :: (Monad m, Monad n) => (m ~> n) -> MaybeT m ~> MaybeT n
  mtMap f = MaybeT . f . runMaybeT

instance (Monad m) => MonadMaybeI (MaybeT m) where
  maybeI :: MaybeT m ~> MaybeT (MaybeT m)
  maybeI = maybeCommute . ftUnit
instance (Monad m) => MonadMaybeE (MaybeT m) where
  maybeE :: MaybeT (MaybeT m) ~> MaybeT m
  maybeE = ftJoin . maybeCommute

-- }}}

-- ErrorT {{{

mapError :: (Functor m) => (e1 -> e2) -> ErrorT e1 m a -> ErrorT e2 m a
mapError f = ErrorT . mapLeft f ^. runErrorT

errorCommute :: (Functor m) => ErrorT e (ErrorT e m) ~> ErrorT e (ErrorT e m)
errorCommute = ErrorT . ErrorT . ff ^. runErrorT . runErrorT
  where
    ff (Inl e) = Inr (Inl e)
    ff (Inr (Inl e)) = Inl e
    ff (Inr (Inr a)) = Inr $ Inr a

instance (Unit m) => Unit (ErrorT e m) where
  unit a = ErrorT $ unit $ Inr a
instance (Functor m) => Functor (ErrorT e m) where
  map f aM = ErrorT $ mapRight f ^$ runErrorT aM
instance (Functor m, Product m) => Product (ErrorT e m) where
  aM1 <*> aM2 = ErrorT $ ff ^$ runErrorT aM1 <*> runErrorT aM2
    where
      ff (Inl e, _) = Inl e
      ff (_, Inl e) = Inl e
      ff (Inr a, Inr b) = Inr (a, b)
instance (Functor m, Applicative m) => Applicative (ErrorT e m) where
  fM <@> aM = ErrorT $ ff ^@ runErrorT fM <$> runErrorT aM
    where
      ff (Inl e) _ = Inl e
      ff _ (Inl e) = Inl e
      ff (Inr f) (Inr a) = Inr $ f a
instance (Unit m, Bind m) => Bind (ErrorT e m) where
  aM >>= k = ErrorT $ do
    aeM <- runErrorT aM
    case aeM of
      Inl e -> unit $ Inl e
      Inr a -> runErrorT $ k a
instance (Monad m) => Monad (ErrorT e m) where
instance MonadUnit (ErrorT e) where
  mtUnit :: (Monad m) => m ~> ErrorT e m
  mtUnit aM = ErrorT $ Inr ^$ aM
instance MonadJoin (ErrorT e) where
  mtJoin :: (Monad m) => ErrorT e (ErrorT e m) ~> ErrorT e m
  mtJoin = ErrorT . ff ^. runErrorT . runErrorT
    where
      ff (Inl e) = Inl e
      ff (Inr ea) = ea
instance MonadFunctor (ErrorT e) where
  mtMap :: (Monad m, Monad n) => m ~> n -> ErrorT e m ~> ErrorT e n
  mtMap f = ErrorT . f . runErrorT

instance (Monad m) => MonadErrorI e (ErrorT e m) where
  errorI :: ErrorT e m ~> ErrorT e (ErrorT e m)
  errorI = errorCommute . mtUnit
instance (Monad m) => MonadErrorE e (ErrorT e m) where
  errorE :: ErrorT e (ErrorT e m) ~> ErrorT e m
  errorE = mtJoin . errorCommute
instance (Monad m) => MonadError e (ErrorT e m) where

-- }}}

-- ReaderT {{{

type Reader r = ReaderT r ID

runReader :: r -> Reader r a -> a
runReader r = runID . runReaderT r

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
instance MonadUnit (ReaderT r) where
  mtUnit = ReaderT . const
instance MonadJoin (ReaderT r) where
  mtJoin aMM = ReaderT $ \ r -> runReaderT r $ runReaderT r aMM
instance MonadFunctor (ReaderT r) where
  mtMap :: (Monad m, Monad n) => (m ~> n) -> (ReaderT r m ~> ReaderT r n)
  mtMap f aM = ReaderT $ \ r -> f $ runReaderT r aM

instance (Monad m) => MonadReaderI r (ReaderT r m) where
  readerI :: ReaderT r m ~> ReaderT r (ReaderT r m)
  readerI = readerCommute . mtUnit
instance (Monad m) => MonadReaderE r (ReaderT r m) where
  readerE :: ReaderT r (ReaderT r m) ~> ReaderT r m
  readerE = mtJoin . readerCommute
instance (Monad m) => MonadReader r (ReaderT r m) where

instance (MonadZero m) => MonadZero (ReaderT r m) where
  mzero = ReaderT $ const mzero

-- }}}

-- WriterT {{{

execWriterT :: (Functor m) => WriterT o m a -> m o
execWriterT = snd ^. runWriterT

mapOutput :: (Functor m) => (o1 -> o2) -> WriterT o1 m a -> WriterT o2 m a
mapOutput f = WriterT . mapSnd f ^. runWriterT

writerCommute :: (Functor m) => WriterT o1 (WriterT o2 m) ~> WriterT o2 (WriterT o1 m)
writerCommute aMM = WriterT $ WriterT $ ff ^$ runWriterT $ runWriterT aMM
  where
    ff ((a, o1), o2) = ((a, o2), o1)

instance (Unit m, Monoid o) => Unit (WriterT o m) where
  unit = WriterT . unit . (,null)
instance (Functor m) => Functor (WriterT o m) where
  map f = WriterT . mapFst f ^. runWriterT
instance (Functor m, Product m, Monoid o) => Product (WriterT o m) where
  aM1 <*> aM2 = WriterT $ ff ^$ runWriterT aM1 <*> runWriterT aM2
    where
      ff ((a1, o1), (a2, o2)) = ((a1, a2), o1 ++ o2)
instance (Functor m, Applicative m, Monoid o) => Applicative (WriterT o m) where
  fM <@> aM = WriterT $ ff2 ^$ ff1 ^@ runWriterT fM <$> runWriterT aM
    where
      ff1 (f, o) = mapFst ((,o) . f)
      ff2 ((a, o1), o2) = (a, o1 ++ o2)
instance (Monad m, Monoid o) => Bind (WriterT o m) where
  aM >>= k = WriterT $ do
    (a, o1) <- runWriterT aM
    (b, o2) <- runWriterT $ k a
    return (b, o1 ++ o2)
instance (Monad m, Monoid o) => Monad (WriterT o m) where
instance (Monoid w) => MonadUnit (WriterT w) where
  mtUnit = WriterT .^ (,null)
instance MonadJoin (WriterT w) where
  mtJoin = fst ^. runWriterT
instance MonadFunctor (WriterT w) where
  mtMap :: (Monad m, Monad n) => (m ~> n) -> (WriterT w m ~> WriterT w n)
  mtMap f aM = WriterT $ f $ runWriterT aM

instance (Monad m, Monoid o) => MonadWriterI o (WriterT o m) where
  writerI :: WriterT o m ~> WriterT o (WriterT o m)
  writerI = writerCommute . mtUnit
instance (Monad m, Monoid o) => MonadWriterE o (WriterT o m) where
  writerE :: WriterT o (WriterT o m) ~> WriterT o m
  writerE = mtJoin . writerCommute
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

type State s = StateT s ID

runState :: s -> State s a -> (a, s)
runState = runID .: runStateT

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
instance MonadUnit (StateT s) where
  mtUnit aM = StateT $ \ s -> (,s) ^$ aM
instance MonadJoin (StateT s) where
  mtJoin aMM = StateT $ \ s -> runStateT s $ fst ^$ runStateT s aMM
instance MonadFunctor (StateT s) where
  mtMap :: (Monad m, Monad n) => (m ~> n) -> StateT s m ~> StateT s n
  mtMap f aM = StateT $ f . unStateT aM

instance (MonadZero m) => MonadZero (StateT s m) where
  mzero = StateT $ const mzero
instance (MonadPlus m) => MonadPlus (StateT s m) where
  aM1 <+> aM2 = StateT $ \ s -> unStateT aM1 s <+> unStateT aM2 s
instance (MonadMonoid m) => MonadMonoid (StateT s m) where
  aM1 <++> aM2 = StateT $ \ s -> unStateT aM1 s <++> unStateT aM2 s

instance (Functorial HasBot m, HasBot s, HasBot a) => HasBot (StateT s m a) where
  bot :: StateT s m a
  bot = 
    with (functorial :: W (HasBot (m (a, s)))) $
    StateT $ \ _ -> bot
instance (Functorial Monoid m, Monoid s, Monoid a) => Monoid (StateT s m a) where
  null =
    with (functorial :: W (Monoid (m (a, s)))) $
    StateT $ \ _ -> null
  aM1 ++ aM2 =
    with (functorial :: W (Monoid (m (a, s)))) $
    StateT $ \ s -> unStateT aM1 s ++ unStateT aM2 s
instance (Functorial Monoid m, Monoid s) => Functorial Monoid (StateT s m) where
  functorial = W
instance (Functorial HasBot m, Functorial JoinLattice m, JoinLattice s, JoinLattice a) => JoinLattice (StateT s m a) where
  aM1 \/ aM2 = 
    with (functorial :: W (JoinLattice (m (a, s)))) $
    StateT $ \ s -> unStateT aM1 s \/ unStateT aM2 s
instance (Functorial HasBot m, Functorial JoinLattice m, JoinLattice s) => Functorial JoinLattice (StateT s m) where
  functorial = W

instance (Monad m) => MonadStateI s (StateT s m) where
  stateI :: StateT s m ~> StateT s (StateT s m) 
  stateI = stateCommute . mtUnit
instance (Monad m) => MonadStateE s (StateT s m) where
  stateE :: StateT s (StateT s m) ~> StateT s m
  stateE = mtJoin . stateCommute
instance (Monad m) => MonadState s (StateT s m) where

-- }}} --

-- RWST {{{

runRWST :: (Functor m) => r -> s -> RWST r o s m a -> m (a, o, s)
runRWST r0 s0 = ff ^. runStateT s0 . runWriterT . runReaderT r0 . unRWST
  where
    ff ((a, o), s) = (a, o, s)
rwsCommute :: (Monad m, Monoid o1, Monoid o2) => RWST r1 o1 s1 (RWST r2 o2 s2 m) ~> RWST r2 o2 s2 (RWST r1 o1 s1 m)
rwsCommute =
  RWST
  . mtMap (mtMap rwsStateCommute . rwsWriterCommute)
  . rwsReaderCommute
  . mtMap unRWST

deriving instance (Unit m, Monoid o) => Unit (RWST r o s m)
deriving instance (Functor m) => Functor (RWST r o s m)
deriving instance (Monad m, Monoid o) => Product (RWST r o s m)
deriving instance (Monad m, Monoid o) => Applicative (RWST r o s m)
deriving instance (Monad m, Monoid o) => Bind (RWST r o s m)
deriving instance (Monad m, Monoid o) => Monad (RWST r o s m)
instance (Monoid o) => MonadUnit (RWST r o s) where
  mtUnit = RWST . mtUnit . mtUnit . mtUnit
instance (Monoid o) => MonadJoin (RWST r o s) where
  mtJoin =
    RWST
    . mtJoin
    . mtMap (mtMap mtJoin . writerReaderCommute)
    . mtMap (mtMap (mtMap (mtMap mtJoin . stateWriterCommute) . stateReaderCommute))
    . unRWST . mtMap unRWST
instance (Monoid o) => MonadFunctor (RWST r o s) where
  mtMap f = RWST . mtMap (mtMap (mtMap f)) . unRWST

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
  rwsI = rwsCommute . mtUnit
instance (Monad m, Monoid o) => MonadRWSE r o s (RWST r o s m) where
  rwsE :: RWST r o s (RWST r o s m) ~> RWST r o s m
  rwsE = mtJoin . rwsCommute
instance (Monad m, Monoid o) => MonadRWS r o s (RWST r o s m) where

deriving instance (MonadZero m, Monoid o) => MonadZero (RWST r o s m)
deriving instance (MonadMaybeI m, Monoid o) => MonadMaybeI (RWST r o s m)
deriving instance (MonadMaybeE m, Monoid o) => MonadMaybeE (RWST r o s m)
deriving instance (MonadMaybe m, Monoid o) => MonadMaybe (RWST r o s m)

-- }}}

-- ListT {{{

listCommute :: (Functor m) => ListT (ListT m) ~> ListT (ListT m)
listCommute = ListT . ListT . transpose ^. runListT . runListT

instance (Unit m) => Unit (ListT m) where
  unit = ListT . unit . singleton
instance (Functor m) => Functor (ListT m) where
  map f = ListT . f ^^. runListT
instance (Monad m, Functorial Monoid m) => Product (ListT m) where
  (<*>) = mpair
instance (Monad m, Functorial Monoid m) => Applicative (ListT m) where
  (<@>) = mapply
instance (Bind m, Functorial Monoid m) => Bind (ListT m) where
  (>>=) :: forall a b. ListT m a -> (a -> ListT m b) -> ListT m b
  aM >>= k = ListT $ do
    xs <- runListT aM
    runListT $ concat $ k ^$ xs
instance (Monad m, Functorial Monoid m) => Monad (ListT m) where
instance FunctorUnit ListT where
  ftUnit = ListT .^ unit
instance FunctorJoin ListT where
  ftJoin = ListT . concat ^. runListT . runListT
instance FunctorFunctor ListT where
  ftMap f = ListT . f . runListT

instance (Functorial Monoid m) => Monoid (ListT m a) where
  null = 
    with (functorial :: W (Monoid (m [a]))) $
    ListT null
  xs ++ ys = 
    with (functorial :: W (Monoid (m [a]))) $
    ListT $ runListT xs ++ runListT ys
instance (Functorial Monoid m) => Functorial Monoid (ListT m) where functorial = W
instance (Functorial Monoid m) => MonadZero (ListT m) where
  mzero =  null
instance (Functorial Monoid m) => MonadMonoid (ListT m) where
  (<++>) = (++)

instance (Monad m, Functorial Monoid m) => MonadListI (ListT m) where
  listI :: ListT m ~> ListT (ListT m)
  listI = listCommute . ftUnit
instance (Monad m, Functorial Monoid m) => MonadListE (ListT m) where
  listE :: ListT (ListT m) ~> ListT m
  listE = ftJoin . listCommute
instance (Monad m, Functorial Monoid m) => MonadList (ListT m) where

maybeToList :: (Functor m) => MaybeT m a -> ListT m a
maybeToList aM = ListT $ ff ^$ runMaybeT aM
  where
    ff Nothing = []
    ff (Just a) = [a]

instance (Monad m, Functorial Monoid m) => MonadMaybeE (ListT m) where
  maybeE :: MaybeT (ListT m) ~> ListT m
  maybeE = listE . maybeToList

-- }}}

-- ErrorListT {{{

errorListCommute :: (Functor m) => ErrorListT e (ErrorListT e m) ~> ErrorListT e (ErrorListT e m)
errorListCommute aMM = ErrorListT $ ErrorListT $ errorListTranspose ^$ runErrorListT $ runErrorListT aMM

instance (Unit m) => Unit (ErrorListT e m) where
  unit = ErrorListT . unit . unit
instance (Functor m) => Functor (ErrorListT e m) where
  map f = ErrorListT . f ^^. runErrorListT
instance (Monad m, Functorial Monoid m) => Product (ErrorListT e m) where
  (<*>) = mpair
instance (Monad m, Functorial Monoid m) => Applicative (ErrorListT e m) where
  (<@>) = mapply
instance (Bind m, Functorial Monoid m) => Bind (ErrorListT e m) where
  (>>=) :: forall a b. ErrorListT e m a -> (a -> ErrorListT e m b) -> ErrorListT e m b
  aM >>= k = ErrorListT $ do
    xs <- runErrorListT aM
    runErrorListT $ concat $ k ^$ xs
instance (Monad m, Functorial Monoid m) => Monad (ErrorListT e m) where
instance FunctorUnit (ErrorListT e) where
  ftUnit = ErrorListT .^ unit
instance FunctorJoin (ErrorListT e) where
  ftJoin = ErrorListT . errorListConcat ^. runErrorListT . runErrorListT
instance FunctorFunctor (ErrorListT e) where
  ftMap f = ErrorListT . f . runErrorListT

instance (Functorial Monoid m) => Monoid (ErrorListT e m a) where
  null = 
    with (functorial :: W (Monoid (m (ErrorList e a)))) $
    ErrorListT null
  xs ++ ys =
    with (functorial :: W (Monoid (m (ErrorList e a)))) $
    ErrorListT $ runErrorListT xs ++ runErrorListT ys
instance (Functorial Monoid m) => Functorial Monoid (ErrorListT e m) where functorial = W
instance (Functorial Monoid m) => MonadZero (ErrorListT e m) where
  mzero = null
instance (Functorial Monoid m) => MonadMonoid (ErrorListT e m) where
  (<++>) = (++)

instance (Monad m, Functorial Monoid m) => MonadErrorListI e (ErrorListT e m) where
  errorListI :: ErrorListT e m ~> ErrorListT e (ErrorListT e m)
  errorListI = errorListCommute . ftUnit
instance (Monad m, Functorial Monoid m) => MonadErrorListE e (ErrorListT e m) where
  errorListE :: ErrorListT e (ErrorListT e m) ~> ErrorListT e m
  errorListE = ftJoin . errorListCommute
instance (Monad m, Functorial Monoid m) => MonadErrorList e (ErrorListT e m) where

errorToErrorList :: (Functor m) => ErrorT e m ~> ErrorListT e m
errorToErrorList aM = ErrorListT $ ff ^$ runErrorT aM
  where
    ff (Inl e) = ErrorListFailure [e]
    ff (Inr a) = ErrorListSuccess a []

-- this might not be right
errorListToError :: (Monad m, Functorial Monoid m) => ErrorListT e (ErrorListT e m) a -> ErrorT e (ErrorListT e m) a
errorListToError aM = ErrorT $ mconcat . ff *$ runErrorListT aM
  where
    ff (ErrorListFailure e) = map (return . Inl) e
    ff (ErrorListSuccess x xs) = map (return . Inr) $ x:xs

instance (Monad m, Functorial Monoid m) => MonadErrorE e (ErrorListT e m) where
  errorE :: ErrorT e (ErrorListT e m) ~> ErrorListT e m
  errorE = errorListE . errorToErrorList
-- instance (Monad m, Functorial Monoid m) => MonadErrorI e (ErrorListT e m) where
--   errorI :: ErrorListT e m ~> ErrorT e (ErrorListT e m)
--   errorI = errorListToError . errorListI
-- instance (Monad m, Functorial Monoid m) => MonadError e (ErrorListT e m) where

-- }}}
 
-- ListSetT {{{

listSetCommute :: (Functor m) => ListSetT (ListSetT m) ~> ListSetT (ListSetT m)
listSetCommute = ListSetT . ListSetT . (ListSet . ListSet ^. transpose . runListSet ^. runListSet) ^. runListSetT . runListSetT

instance (Unit m) => Unit (ListSetT m) where
  unit = ListSetT . unit . ListSet . singleton
instance (CUnit c m) => CUnit (c ::.:: ListSet) (ListSetT m) where
  cunit = ListSetT . cunit . ListSet . singleton
instance (Functor m) => Functor (ListSetT m) where
  map f = ListSetT . f ^^. runListSetT
instance (Monad m, Functorial JoinLattice m) => Product (ListSetT m) where
  (<*>) = mpair
instance (Monad m, Functorial JoinLattice m) => Applicative (ListSetT m) where
  (<@>) = mapply
instance (Bind m, Functorial JoinLattice m) => Bind (ListSetT m) where
  (>>=) :: forall a b. ListSetT m a -> (a -> ListSetT m b) -> ListSetT m b
  aM >>= k = ListSetT $ do
    xs <- runListSetT aM
    runListSetT $ msum $ k ^$ xs
-- PROOF of: monad laws for (ListSetT m) {{{
--
-- ASSUMPTION 1: returnₘ a <+> returnₘ b = returnₘ (a \/ b)
-- [this comes from m being a lattice functor. (1 x + 1 y) = 1 (x + y)]
--
-- * PROOF of: left unit := return x >>= k = k x {{{
--   
--   return x >>= k
--   = [[definition of >>=]]
--   ListSetT $ do { xs <- runListSetT $ return x ; runListSetT $ msums $ map k xs }
--   = [[definition of return]]
--   ListSetT $ do { xs <- runListSetT $ ListSetT $ return [x] ; runListSetT $ msums $ map k xs }
--   = [[ListSetT beta]]
--   ListSetT $ do { xs <- return [x] ; runListSetT $ msums $ map k xs }
--   = [[monad left unit]]
--   ListSetT $ runListSetT $ msums $ map k [x]
--   = [[definition of map]]
--   ListSetT $ runListSetT $ msums $ [k x]
--   = [[definition of msums and <+> unit]]
--   ListSetT $ runListSetT $ k x
--   = [[ListSetT eta]]
--   k x
--   QED }}}
--
-- * PROOF of: right unit := aM >>= return = aM {{{
--
--   aM >>= return
--   = [[definition of >>=]]
--   ListSetT $ { xs <- runListSetT aM ; runListSetT $ msums $ map return xs }
--   = [[induction/expansion on xs]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ msums $ map return [x1,..,xn] }
--   = [[definition of return and map]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ msums $ [ListSetT $ return [x1],..,ListSetT $ return [xn]] }
--   = [[definition of msums]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ ListSetT $ return [x1] <+> .. <+> return [xn] }
--   = [[assumption 1]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ ListSetT $ return [x1,..,xn] }
--   = [[ListSetT beta]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; return [x1,..,xn] }
--   = [[monad right unit]]
--   ListSetT $ runListSetT aM
--   = [[ListSetT eta]]
--   aM
--   QED }}}
--
-- * PROOF of: associativity := (aM >>= k1) >>= k2 = { x <- aM ; k1 x >>= k2 } {{{
--
--   (aM >>= k1) >>= k2
--   = [[definition of >>=]]
--   ListSetT $ { xs <- runListSetT $ ListSetT $ { xs' <- runListSetT aM ; runListSetT $ msums $ map k1 xs' } ; runListSetT $ msums $ map k xs }
--   = [[ListSetT beta]]
--   ListSetT $ { xs <- { xs' <- runListSetT aM ; runListSetT $ msums $ map k1 xs' } ; runListSetT $ msums $ map k xs }
--   = [[monad associativity]]
--   ListSetT $ { xs' <- runListSetT aM ; xs <- runListSetT $ msums $ map k1 xs' ; runListSetT $ msums $ map k xs }
--   =
--   LHS
--
--   { x <- aM ; k1 x >>= k2 }
--   = [[definition of >>=]]
--   ListSetT $ { xs' <- runListSetT aM ; runListSetT $ msums $ map (\ x -> ListSetT $ { xs <- runListSetT (k1 x) ; runListSetT $ msums $ map k2 xs }) xs' }
--   = [[induction/expansion on xs']]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ msums $ map (\ x -> ListSetT $ { xs <- runListSetT (k1 x) ; runListSetT $ msums $ map k2 xs }) [x1,..,xn] }
--   = [[definition of map]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ msums $ [ListSetT $ { xs <- runListSetT (k1 x1) ; runListSetT $ msums $ map k2 xs },..,ListSetT $ { xs <- runListSetT (k1 xn) ; runList $ msums $ map k2 xs}] }
--   = [[definition of msum]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; runListSetT $ ListSetT { xs <- runListSetT (k1 x1) ; runListSetT $ msums $ map k2 xs } <+> .. <+> ListSetT { xs <- runListSetT (k1 xn) ; runListSetT $ msums $ map k2 xs } }
--   = [[ListSetT beta and definition of <+> for ListSetT]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; { xs <- runListSetT (k1 x1) ; runListSetT $ msums $ map k2 xs } <+> .. <+> { xs <- runListSetT (k1 xn) ; runListSetT $ msums $ map k2 xs } }
--   = [[<+> distribute with >>=]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; xs <- (runListSetT (k1 x1) <+> .. <+> runListSetT (k1 xn)) ;  runListSetT $ msums $ map k2 xs }
--   = [[definition of msums and map]]
--   ListSetT $ { [x1,..,xn] <- runListSetT aM ; xs <- runListSetT $ msums $ map k1 [x1,..,xn] ; runListSetT $ msums $ map k2 xs }
--   = [[collapsing [x1,..,xn]]]
--   ListSetT $ { xs' <- runListSetT aM ; xs <- runListSetT $ msums $ map k1 xs' ; runListSetT $ msums $ map k xs }
--   =
--   RHS
--
--   LHS = RHS
--   QED }}}
--
-- }}}
instance (Monad m, Functorial JoinLattice m) => Monad (ListSetT m) where
instance MonadUnit ListSetT where
  mtUnit = ListSetT .^ unit
instance MonadJoin ListSetT where
  mtJoin = ListSetT . concat ^. runListSetT . runListSetT
instance MonadFunctor ListSetT where
  mtMap f = ListSetT . f . runListSetT

instance (Functorial JoinLattice m) => MonadZero (ListSetT m) where
  mzero :: forall a. ListSetT m a
  mzero = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT bot
instance (Functorial JoinLattice m) => MonadPlus (ListSetT m) where
  (<+>) :: forall a. ListSetT m a -> ListSetT m a -> ListSetT m a
  aM1 <+> aM2 = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT $ runListSetT aM1 \/ runListSetT aM2

instance (Monad m, Functorial JoinLattice m) => MonadListSetI (ListSetT m) where
  listSetI :: ListSetT m ~> ListSetT (ListSetT m)
  listSetI = listSetCommute . mtUnit
instance (Monad m, Functorial JoinLattice m) => MonadListSetE (ListSetT m) where
  listSetE :: ListSetT (ListSetT m) ~> ListSetT m
  listSetE = mtJoin . listSetCommute
instance (Monad m, Functorial JoinLattice m) => MonadListSet (ListSetT m) where

-- }}}

-- SetT {{{

setCommute :: (Functor m) => SetT (SetT m) ~> SetT (SetT m)
setCommute = SetT . SetT . setTranspose ^. runSetT . runSetT

instance (CUnit c m) => CUnit (Ord ::*:: (c ::.:: Set)) (SetT m) where
  cunit = SetT . cunit . ssingleton 
instance (Functor m, Product m) => Product (SetT m) where
  (<*>) :: forall a b. SetT m a -> SetT m b -> SetT m (a, b)
  aM1 <*> aM2 = SetT $ uncurry ff ^$ runSetT aM1 <*> runSetT aM2
    where
      ff :: Set a -> Set b -> Set (a, b)
      ff s1 s2 =
        learnSetOn s1 null $
        learnSetOn s2 null $
        fromList $ toList s1 <*> toList s2
instance (CFunctor c m) => CFunctor (Ord ::*:: (c ::.:: Set)) (SetT m) where
  cmap = mapSetT . cmap . cmap
instance (Functorial JoinLattice m, Bind m) => Bind (SetT m) where
  aM >>= k = SetT $ do
    aC <- runSetT aM
    runSetT $ msum $ k ^$ toList aC
instance (Functorial JoinLattice m) => MonadZero (SetT m) where
  mzero :: forall a. SetT m a
  mzero = 
    with (functorial :: W (JoinLattice (m (Set a)))) $
    SetT bot
instance (Functorial JoinLattice m) => MonadPlus (SetT m) where
  (<+>) :: forall a. SetT m a -> SetT m a -> SetT m a
  aM1 <+> aM2 =
    with (functorial :: W (JoinLattice (m (Set a)))) $
    SetT $ runSetT aM1 \/ runSetT aM2

-- }}}

-- KonT {{{

evalKonT :: (Unit m) => KonT r m r -> m r
evalKonT aM = runKonT aM unit

type Kon r = KonT r ID
runKon :: Kon r a -> (a -> r) -> r
runKon aM f = runID $ runKonT aM (ID . f)
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
  aM >>= kM = KonT $ \ (k :: b -> m r) -> runKonT aM $ \ a -> runKonT (kM a) k
instance (Unit m) => Monad (KonT r m) where
instance MonadIsoFunctor (KonT r) where
  mtIsoMap :: (Monad m, Monad n) => m ~> n -> n ~> m -> KonT r m ~> KonT r n
  mtIsoMap to from aM = KonT $ \ (k :: a -> n r) -> to $ runKonT aM $ \ a -> from $ k a

instance (Monad m) => MonadKonI r (KonT r m) where
  konI :: KonT r m ~> KonT r (KonT r m)
  konI aM = KonT $ \ (k1 :: a -> KonT r m r) -> KonT $ \ (k2 :: r -> m r) ->
    k2 *$ runKonT aM $ \ a -> runKonT (k1 a) return
instance (Monad m) => MonadKonE r (KonT r m) where
  konE :: KonT r (KonT r m) ~> KonT r m
  konE aMM = KonT $ \ (k :: a -> m r) -> 
    let aM :: KonT r m r
        aM = runKonT aMM $ \ a -> KonT $ \ (k' :: r -> m r) -> k' *$ k a
    in runKonT aM return
instance (Monad m) => MonadKon r (KonT r m) where

-- }}}

-- OpaqueKonT {{{

runOpaqueKonTWith :: k r m a -> OpaqueKonT k r m a -> m r
runOpaqueKonTWith = flip runOpaqueKonT
makeMetaKonT :: (FFMorphism (k r) (KFun r)) => ((a -> m r) -> m r) -> OpaqueKonT k r m a
makeMetaKonT nk = OpaqueKonT $ \ (k :: k r m a) -> nk $ runKFun $ ffmorph k
runMetaKonT :: (FFMorphism (KFun r) (k r)) => OpaqueKonT k r m a -> (a -> m r) -> m r
runMetaKonT aM k = runOpaqueKonT aM $ ffmorph $ KFun k
runMetaKonTWith :: (FFMorphism (KFun r) (k r)) => (a -> m r) -> OpaqueKonT k r m a -> m r
runMetaKonTWith = flip runMetaKonT
evalOpaqueKonT :: (Unit m, FFMorphism (KFun r) (k r)) => OpaqueKonT k r m r -> m r
evalOpaqueKonT aM = runMetaKonT aM unit

type OpaqueKon k r = OpaqueKonT k r ID

makeOpaqueKon :: (k r ID a -> r) -> OpaqueKon k r a
makeOpaqueKon nk = OpaqueKonT $ ID . nk
makeMetaKon :: (FFMorphism (k r) (KFun r)) => ((a -> r) -> r) -> OpaqueKon k r a
makeMetaKon nk = makeOpaqueKon $ \ (k :: k r ID a) -> nk $ (.) runID . runKFun $ ffmorph k
runOpaqueKon :: OpaqueKon k r a -> k r ID a -> r
runOpaqueKon = runID .: runOpaqueKonT
runMetaKon :: (FFMorphism (KFun r) (k r)) => OpaqueKon k r a -> (a -> r) -> r
runMetaKon aM k = runOpaqueKon aM $ ffmorph $ KFun $ ID . k
evalOpaqueKon :: (FFMorphism (KFun r) (k r)) => OpaqueKon k r r -> r
evalOpaqueKon aM = runMetaKon aM id

metaKonT :: (FFMorphism (KFun r) (k r)) => OpaqueKonT k r m ~> KonT r m
metaKonT aM = KonT $ \ (k :: a -> m r) -> runMetaKonT aM k

opaqueKonT :: (FFMorphism (k r) (KFun r)) => KonT r m ~> OpaqueKonT k r m
opaqueKonT aM = makeMetaKonT $ \ (k :: a -> m r) -> runKonT aM k

instance (Monad m, FFMorphism (k r) (KFun r)) => Unit (OpaqueKonT k r m) where
  unit :: a -> OpaqueKonT k r m a
  unit = opaqueKonT . unit
instance (Monad m, FFIsomorphism (KFun r) (k r)) => Functor (OpaqueKonT k r m) where
  map = mmap
instance (Monad m, FFIsomorphism (KFun r) (k r)) => Applicative (OpaqueKonT k r m) where
  (<@>) = mapply
instance (Monad m, FFIsomorphism (KFun r) (k r)) => Product (OpaqueKonT k r m) where
  (<*>) = mpair
instance (Monad m, FFIsomorphism (KFun r) (k r)) => Bind (OpaqueKonT k r m) where
  (>>=) :: OpaqueKonT k r m a -> (a -> OpaqueKonT k r m b) -> OpaqueKonT k r m b
  aM >>= kM = OpaqueKonT $ \ (k :: k r m a) -> runMetaKonT aM $ \ a -> runOpaqueKonT (kM a) k
instance (Monad m, FFIsomorphism (KFun r) (k r)) => Monad (OpaqueKonT k r m) where
instance (FFIsomorphism (k r) (KFun r)) => MonadIsoFunctor (OpaqueKonT k r) where
  mtIsoMap :: (Monad m, Monad n) => m ~> n -> n ~> m -> OpaqueKonT k r m ~> OpaqueKonT k r n
  mtIsoMap to from = opaqueKonT . mtIsoMap to from . metaKonT

class Balloon k r | k -> r where
  inflate :: (Monad m) => k r m ~> k r (OpaqueKonT k r m)
  deflate :: (Monad m) => k r (OpaqueKonT k r m) ~> k r m
instance (Monad m, FFIsomorphism (KFun r) (k r), Balloon k r) => MonadOpaqueKonI k r (OpaqueKonT k r m) where
  withOpaqueC :: k r (OpaqueKonT k r m) a -> OpaqueKonT k r m a -> OpaqueKonT k r m r
  withOpaqueC k1 aM = makeMetaKonT $ \ (k2 :: r -> m r) -> k2 *$ runOpaqueKonT aM $ deflate k1
instance (Monad m, FFIsomorphism (KFun r) (k r), Balloon k r) => MonadOpaqueKonE k r (OpaqueKonT k r m) where
  callOpaqueCC :: (k r (OpaqueKonT k r m) a -> OpaqueKonT k r m r) -> OpaqueKonT k r m a
  callOpaqueCC kk = OpaqueKonT $ \ (k :: k r m a ) -> runMetaKonTWith return $ kk $ inflate k
instance (Monad m, FFIsomorphism (KFun r) (k r), Balloon k r) => MonadOpaqueKon k r (OpaqueKonT k r m) where

instance (Monad m, FFIsomorphism (KFun r) (k r)) => MonadKonI r (OpaqueKonT k r m) where
  konI :: OpaqueKonT k r m ~> KonT r (OpaqueKonT k r m)
  konI aM = KonT $ \ (k1 :: a -> OpaqueKonT k r m r) -> makeMetaKonT $ \ (k2 :: r -> m r) ->
    k2 *$ runMetaKonT aM $ \ a -> runMetaKonT (k1 a) return
instance (Monad m, FFIsomorphism (KFun r) (k r)) => MonadKonE r (OpaqueKonT k r m) where
  konE :: KonT r (OpaqueKonT k r m) ~> OpaqueKonT k r m
  konE aMM = makeMetaKonT $ \ (k :: a -> m r) ->
    runMetaKonTWith return $ runKonT aMM $ \ a -> makeMetaKonT $ \ (k' :: r -> m r) -> k' *$ k a
instance (Monad m, FFIsomorphism (KFun r) (k r)) => MonadKon r (OpaqueKonT k r m) where

-- }}}

----------------------
-- Monads Commuting --
----------------------

-- Maybe // * --

-- Maybe // Reader // FULL COMMUTE {{{

maybeReaderCommute :: (Monad m) => MaybeT (ReaderT r m) ~> ReaderT r (MaybeT m)
maybeReaderCommute aMRM = ReaderT $ \ r -> MaybeT $ runReaderT r $ runMaybeT aMRM

readerMaybeCommute :: (Monad m) => ReaderT r (MaybeT m) ~> MaybeT (ReaderT r m)
readerMaybeCommute aRMM = MaybeT $ ReaderT $ \ r -> runMaybeT $ runReaderT r aRMM

instance (MonadReaderI r m) => MonadReaderI r (MaybeT m) where
  readerI :: MaybeT m ~> ReaderT r (MaybeT m)
  readerI = maybeReaderCommute . mtMap readerI
instance (MonadReaderE r m) => MonadReaderE r (MaybeT m) where
  readerE :: ReaderT r (MaybeT m) ~> MaybeT m
  readerE = mtMap readerE . readerMaybeCommute
instance (MonadReader r m) => MonadReader r (MaybeT m) where

instance (MonadMaybeI m) => MonadMaybeI (ReaderT r m) where
  maybeI :: ReaderT r m ~> MaybeT (ReaderT r m)
  maybeI = readerMaybeCommute . mtMap maybeI
instance (MonadMaybeE m) => MonadMaybeE (ReaderT r m) where
  maybeE :: MaybeT (ReaderT r m) ~> ReaderT r m
  maybeE = mtMap maybeE . maybeReaderCommute
instance (MonadMaybe m) => MonadMaybe (ReaderT r m) where

-- }}}

-- Maybe // Writer {{{

writerMaybeCommute :: (Monoid w, Monad m) => WriterT w (MaybeT m) ~> MaybeT (WriterT w m)
writerMaybeCommute aRMM = MaybeT $ WriterT $ do
  awM <- runMaybeT $ runWriterT aRMM
  return $ case awM of
    Nothing -> (Nothing, null)
    Just (a, w) -> (Just a, w)

maybeWriterCommute :: (Monad m) => MaybeT (WriterT w m) ~> WriterT w (MaybeT m)
maybeWriterCommute aMRM = WriterT $ MaybeT $ do
  (aM, w) <- runWriterT $ runMaybeT aMRM
  return $ case aM of
    Nothing -> Nothing
    Just a -> Just (a, w)

instance (Monoid w, MonadWriter w m) => MonadWriterI w (MaybeT m) where
  writerI :: MaybeT m ~> WriterT w (MaybeT m)
  writerI = maybeWriterCommute . mtMap writerI
instance (Monoid w, MonadWriter w m) => MonadWriterE w (MaybeT m) where
  writerE :: WriterT w (MaybeT m) ~> MaybeT m
  writerE = mtMap writerE . writerMaybeCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (MaybeT m) where

instance (Monoid w, MonadMaybeI m) => MonadMaybeI (WriterT w m) where
  maybeI :: WriterT w m ~> MaybeT (WriterT w m)
  maybeI = writerMaybeCommute . mtMap maybeI
instance (Monoid w, MonadMaybeE m) => MonadMaybeE (WriterT w m) where
  maybeE :: MaybeT (WriterT w m) ~> WriterT w m
  maybeE = mtMap maybeE . maybeWriterCommute
instance (Monoid w, MonadMaybe m) => MonadMaybe (WriterT w m) where

-- }}}

-- Maybe // State {{{

maybeStateCommute :: (Monad m) => MaybeT (StateT s m) ~> StateT s (MaybeT m)
maybeStateCommute aMSM = StateT $ \ s1 -> MaybeT $ do
  (aM, s2) <- runStateT s1 $ runMaybeT aMSM
  return $ case aM of
    Nothing -> Nothing
    Just a -> Just (a, s2)

stateMaybeCommute :: (Monad m) => StateT s (MaybeT m) ~> MaybeT (StateT s m)
stateMaybeCommute aSMM = MaybeT $ StateT $ \ s1 -> do
  asM <- runMaybeT $ runStateT s1 aSMM
  return $ case asM of
    Nothing -> (Nothing, s1)
    Just (a, s2) -> (Just a, s2)

instance (MonadStateI s m) => MonadStateI s (MaybeT m) where
  stateI :: MaybeT m ~> StateT s (MaybeT m)
  stateI = maybeStateCommute . mtMap stateI
instance (MonadStateE s m) => MonadStateE s (MaybeT m) where
  stateE :: StateT s (MaybeT m) ~> MaybeT m
  stateE = mtMap stateE . stateMaybeCommute
instance (MonadState s m) => MonadState s (MaybeT m) where

instance (MonadMaybeI m) => MonadMaybeI (StateT s m) where
  maybeI :: StateT s m ~> MaybeT (StateT s m)
  maybeI = stateMaybeCommute . mtMap maybeI
instance (MonadMaybeE m) => MonadMaybeE (StateT s m) where
  maybeE :: MaybeT (StateT s m) ~> StateT s m
  maybeE = mtMap maybeE . maybeStateCommute
instance (MonadMaybe m) => MonadMaybe (StateT s m) where

-- }}}

-- Error // * --

-- Error // Reader {{{

errorReaderCommute :: (Monad m) => ErrorT e (ReaderT r m) ~> ReaderT r (ErrorT e m)
errorReaderCommute aMRM = ReaderT $ \ r -> ErrorT $ runReaderT r $ runErrorT aMRM

readerErrorCommute :: (Monad m) => ReaderT r (ErrorT e m) ~> ErrorT e (ReaderT r m)
readerErrorCommute aRMM = ErrorT $ ReaderT $ \ r -> runErrorT $ runReaderT r aRMM

instance (MonadReaderI r m) => MonadReaderI r (ErrorT e m) where
  readerI :: ErrorT e m ~> ReaderT r (ErrorT e m)
  readerI = errorReaderCommute . mtMap readerI
instance (MonadReaderE r m) => MonadReaderE r (ErrorT e m) where
  readerE :: ReaderT r (ErrorT e m) ~> ErrorT e m
  readerE = mtMap readerE . readerErrorCommute
instance (MonadReader r m) => MonadReader r (ErrorT e m) where

instance (MonadErrorI e m) => MonadErrorI e (ReaderT r m) where
  errorI :: ReaderT r m ~> ErrorT e (ReaderT r m)
  errorI = readerErrorCommute . mtMap errorI
instance (MonadErrorE e m) => MonadErrorE e (ReaderT r m) where
  errorE :: ErrorT e (ReaderT r m) ~> ReaderT r m
  errorE = mtMap errorE . errorReaderCommute
instance (MonadError e m) => MonadError e (ReaderT r m) where

-- }}}

-- Error // State {{{

errorStateCommute :: (Monad m) => ErrorT e (StateT s m) ~> StateT s (ErrorT e m)
errorStateCommute aMRM = StateT $ \ s -> ErrorT $ ff ^$ runStateT s $ runErrorT aMRM
  where
    ff :: (e :+: a, s) -> e :+: (a, s)
    ff (Inl e, _) = Inl e
    ff (Inr a, s) = Inr $ (a, s)

stateErrorCommute :: (Monad m) => StateT s (ErrorT e m) ~> ErrorT e (StateT s m)
stateErrorCommute aRMM = ErrorT $ StateT $ \ s -> ff s ^$ runErrorT $ runStateT s aRMM
  where
    ff :: s -> e :+: (a, s) -> (e :+: a, s)
    ff s (Inl e) = (Inl e, s)
    ff _ (Inr (a, s)) = (Inr a, s)

instance (MonadStateI s m) => MonadStateI s (ErrorT e m) where
  stateI :: ErrorT e m ~> StateT s (ErrorT e m)
  stateI = errorStateCommute . mtMap stateI
instance (MonadStateE s m) => MonadStateE s (ErrorT e m) where
  stateE :: StateT s (ErrorT e m) ~> ErrorT e m
  stateE = mtMap stateE . stateErrorCommute
instance (MonadState s m) => MonadState s (ErrorT e m) where

instance (MonadErrorI e m) => MonadErrorI e (StateT s m) where
  errorI :: StateT s m ~> ErrorT e (StateT s m)
  errorI = stateErrorCommute . mtMap errorI
instance (MonadErrorE e m) => MonadErrorE e (StateT s m) where
  errorE :: ErrorT e (StateT s m) ~> StateT s m
  errorE = mtMap errorE . errorStateCommute
instance (MonadError e m) => MonadError e (StateT s m) where

-- }}}

-- Reader // * --

-- Reader // Writer // FULL COMMUTE {{{

readerWriterCommute :: ReaderT r (WriterT w m) ~> WriterT w (ReaderT r m)
readerWriterCommute aRWM = WriterT $ ReaderT $ \ r -> runWriterT $ runReaderT r aRWM

writerReaderCommute :: WriterT w (ReaderT r m) ~> ReaderT r (WriterT w m)
writerReaderCommute aWRM = ReaderT $ \ r -> WriterT $ runReaderT r $ runWriterT aWRM

instance (Monoid w, MonadWriterI w m) => MonadWriterI w (ReaderT r m) where
  writerI :: ReaderT r m ~> WriterT w (ReaderT r m)
  writerI = readerWriterCommute . mtMap writerI
instance (Monoid w, MonadWriterE w m) => MonadWriterE w (ReaderT r m) where
  writerE :: WriterT w (ReaderT r m) ~> ReaderT r m
  writerE = mtMap writerE . writerReaderCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (ReaderT r m) where

instance (Monoid w, MonadReaderI r m) => MonadReaderI r (WriterT w m) where
  readerI :: WriterT w m ~> ReaderT r (WriterT w m)
  readerI = writerReaderCommute . mtMap readerI
instance (Monoid w, MonadReaderE r m) => MonadReaderE r (WriterT w m) where
  readerE :: ReaderT r (WriterT w m) ~> WriterT w m
  readerE = mtMap readerE . readerWriterCommute
instance (Monoid w, MonadReader r m) => MonadReader r (WriterT w m) where

-- }}}

-- Reader // State // FULL COMMUTE {{{

readerStateCommute :: (Functor m) => ReaderT r (StateT s m) ~> StateT s (ReaderT r m)
readerStateCommute aRSM = StateT $ \ s -> ReaderT $ \ r ->
  runStateT s $ runReaderT r aRSM

stateReaderCommute :: (Functor m) => StateT s (ReaderT r m) ~> ReaderT r (StateT s m)
stateReaderCommute aSRM = ReaderT $ \ r -> StateT $ \ s -> 
  runReaderT r $ runStateT s aSRM

instance (MonadStateI s m) => MonadStateI s (ReaderT r m) where
  stateI :: ReaderT r m ~> StateT s (ReaderT r m)
  stateI = readerStateCommute . mtMap stateI
instance (MonadStateE s m) => MonadStateE s (ReaderT r m) where
  stateE :: StateT s (ReaderT r m) ~> ReaderT r m
  stateE = mtMap stateE . stateReaderCommute
instance (MonadState s m) => MonadState s (ReaderT r m) where

instance (MonadReaderI r m) => MonadReaderI r (StateT s m) where
  readerI :: StateT s m ~> ReaderT r (StateT s m)
  readerI = stateReaderCommute . mtMap readerI
instance (MonadReaderE r m) => MonadReaderE r (StateT s m) where
  readerE :: ReaderT r (StateT s m) ~> StateT s m
  readerE = mtMap readerE . readerStateCommute
instance (MonadReader r m) => MonadReader r (StateT s m) where

-- }}}

-- Reader // RWS {{{

readerRWSCommute :: (Monad m, Monoid o) => ReaderT r1 (RWST r2 o s m) ~> RWST r2 o s (ReaderT r1 m)
readerRWSCommute =
    RWST
  . mtMap 
    ( mtMap readerStateCommute
    . readerWriterCommute
    )
  . readerCommute
  . mtMap unRWST

rwsReaderCommute :: (Monad m, Monoid o) => RWST r1 o s (ReaderT r2 m) ~> ReaderT r2 (RWST r1 o s m)
rwsReaderCommute = 
    mtMap RWST
  . readerCommute
  . mtMap 
    ( writerReaderCommute
    . mtMap stateReaderCommute
    )
  . unRWST
       
-- }}}

-- Writer // * --

-- Writer // State // FULL COMMUTE {{{

writerStateCommute :: (Functor m) => WriterT w (StateT s m) ~> StateT s (WriterT w m)
writerStateCommute aRMM = StateT $ \ s1 -> WriterT $ ff ^$ runStateT s1 $ runWriterT aRMM
  where
    ff ((a, w), s) = ((a, s), w)

stateWriterCommute :: (Functor m) => StateT s (WriterT w m) ~> WriterT w (StateT s m)
stateWriterCommute aMRM = WriterT $ StateT $ ff ^. runWriterT . unStateT aMRM
  where
    ff ((a, s), w) = ((a, w), s)

instance (Monoid w, MonadStateI s m) => MonadStateI s (WriterT w m) where
  stateI :: WriterT w m ~> StateT s (WriterT w m)
  stateI = writerStateCommute . mtMap stateI
instance (Monoid w, MonadStateE s m) => MonadStateE s (WriterT w m) where
  stateE :: StateT s (WriterT w m) ~> WriterT w m
  stateE = mtMap stateE . stateWriterCommute
instance (Monoid w, MonadState s m) => MonadState s (WriterT w m) where

instance (Monoid w, MonadWriter w m) => MonadWriterI w (StateT s m) where
  writerI :: StateT s m ~> WriterT w (StateT s m)
  writerI = stateWriterCommute . mtMap writerI
instance (Monoid w, MonadWriter w m) => MonadWriterE w (StateT s m) where
  writerE :: WriterT w (StateT s m) ~> StateT s m
  writerE = mtMap writerE . writerStateCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (StateT s m) where

-- }}}

-- Writer // RWS {{{

writerRWSCommute :: (Monad m, Monoid o1, Monoid o2) => WriterT o1 (RWST r o2 s m) ~> RWST r o2 s (WriterT o1 m)
writerRWSCommute =
    RWST
  . mtMap 
    ( mtMap writerStateCommute
    . writerCommute
    )
  . writerReaderCommute
  . mtMap unRWST

rwsWriterCommute :: (Monad m, Monoid o1, Monoid o2) => RWST r o1 s (WriterT o2 m) ~> WriterT o2 (RWST r o1 s m)
rwsWriterCommute =
    mtMap RWST
  . readerWriterCommute
  . mtMap 
    ( writerCommute
    . mtMap stateWriterCommute
    )
  . unRWST

-- }}}

-- State // * --

-- State // RWS {{{

stateRWSCommute :: (Monad m, Monoid o) => StateT s1 (RWST r o s2 m) ~> RWST r o s2 (StateT s1 m)
stateRWSCommute =
    RWST
  . mtMap 
    ( mtMap stateCommute
    . stateWriterCommute
    )
  . stateReaderCommute
  . mtMap unRWST

rwsStateCommute :: (Monad m, Monoid o) => RWST r o s1 (StateT s2 m) ~> StateT s2 (RWST r o s1 m)
rwsStateCommute =
    mtMap RWST
  . readerStateCommute
  . mtMap 
    ( writerStateCommute
    . mtMap stateCommute
    )
  . unRWST

-- }}}

-- State // List {{{

-- (s -> m [a, s]) -> (s -> m ([a], s))

stateListCommute :: (Functor m, Monoid s) => StateT s (ListT m) ~> ListT (StateT s m)
stateListCommute aMM = ListT $ StateT $ \ s -> ff ^$ runListT $ runStateT s aMM
  where
    ff asL = (fst ^$ asL, concat $ snd ^$ asL)

listStateCommute :: (Functor m) => ListT (StateT s m) ~> StateT s (ListT m)
listStateCommute aMM = StateT $ \ s -> ListT $ ff ^$ runStateT s $ runListT aMM
  where
    ff (xs, s) = (,s) ^$ xs

instance (MonadListI m, Functorial Monoid m, Monoid s) => MonadListI (StateT s m) where
  listI :: StateT s m ~> ListT (StateT s m)
  listI = stateListCommute . mtMap listI
instance (MonadListE m, Functorial Monoid m) => MonadListE (StateT s m) where
  listE :: ListT (StateT s m) ~> StateT s m
  listE = mtMap listE . listStateCommute
instance (MonadList m, Functorial Monoid m, Monoid s) => MonadList (StateT s m) where

instance (MonadStateI s m, Functorial Monoid m) => MonadStateI s (ListT m) where
  stateI :: ListT m ~> StateT s (ListT m)
  stateI = listStateCommute . ftMap stateI
instance (MonadStateE s m, Functorial Monoid m, Monoid s) => MonadStateE s (ListT m) where
  stateE :: StateT s (ListT m) ~> ListT m
  stateE = ftMap stateE . stateListCommute
instance (MonadState s m, Functorial Monoid m, Monoid s) => MonadState s (ListT m) where

-- }}}

-- State // ListSet {{{

stateListSetCommute :: (Functor m, JoinLattice s) => StateT s (ListSetT m) ~> ListSetT (StateT s m)
stateListSetCommute aMM = ListSetT $ StateT $ \ s -> ff ^$ runListSetT $ runStateT s aMM
  where
    ff asL = (fst ^$ asL, joins $ snd ^$ asL)

listSetStateCommute :: (Functor m) => ListSetT (StateT s m) ~> StateT s (ListSetT m)
listSetStateCommute aMM = StateT $ \ s -> ListSetT $ ff ^$ runStateT s $ runListSetT aMM
  where
    ff (xs, s) = (,s) ^$ xs

instance (MonadListSetI m, Functorial JoinLattice m, JoinLattice s) => MonadListSetI (StateT s m) where
  listSetI :: StateT s m ~> ListSetT (StateT s m)
  listSetI = stateListSetCommute . mtMap listSetI
instance (MonadListSetE m, Functorial JoinLattice m) => MonadListSetE (StateT s m) where
  listSetE :: ListSetT (StateT s m) ~> StateT s m
  listSetE = mtMap listSetE . listSetStateCommute
instance (MonadListSet m, Functorial JoinLattice m, JoinLattice s) => MonadListSet (StateT s m) where

instance (MonadStateI s m, Functorial JoinLattice m) => MonadStateI s (ListSetT m) where
  stateI :: ListSetT m ~> StateT s (ListSetT m)
  stateI = listSetStateCommute . mtMap stateI
instance (MonadStateE s m, Functorial JoinLattice m, JoinLattice s) => MonadStateE s (ListSetT m) where
  stateE :: StateT s (ListSetT m) ~> ListSetT m
  stateE = mtMap stateE . stateListSetCommute
instance (MonadState s m, Functorial JoinLattice m, JoinLattice s) => MonadState s (ListSetT m) where

-- }}}

-- State // ErrorList {{{

stateErrorListCommute :: (Functor m, Monoid s) => StateT s (ErrorListT e m) ~> ErrorListT e (StateT s m)
stateErrorListCommute aMM = ErrorListT $ StateT $ \ s -> ff ^$ runErrorListT $ runStateT s aMM
  where
    ff asL = (fst ^$ asL, concat $ snd ^$ asL)

errorListStateCommute :: (Functor m) => ErrorListT e (StateT s m) ~> StateT s (ErrorListT e m)
errorListStateCommute aMM = StateT $ \ s -> ErrorListT $ ff ^$ runStateT s $ runErrorListT aMM
  where
    ff (xs, s) = (,s) ^$ xs

instance (MonadErrorListI e m, Functorial Monoid m, Monoid s) => MonadErrorListI e (StateT s m) where
  errorListI :: StateT s m ~> ErrorListT e (StateT s m)
  errorListI = stateErrorListCommute . mtMap errorListI
instance (MonadErrorListE e m, Functorial Monoid m) => MonadErrorListE e (StateT s m) where
  errorListE :: ErrorListT e (StateT s m) ~> StateT s m
  errorListE = mtMap errorListE . errorListStateCommute
instance (MonadErrorList e m, Functorial Monoid m, Monoid s) => MonadErrorList e (StateT s m) where

instance (MonadStateI s m, Functorial Monoid m) => MonadStateI s (ErrorListT e m) where
  stateI :: ErrorListT e m ~> StateT s (ErrorListT e m)
  stateI = errorListStateCommute . ftMap stateI
instance (MonadStateE s m, Functorial Monoid m, Monoid s) => MonadStateE s (ErrorListT e m) where
  stateE :: StateT s (ErrorListT e m) ~> ErrorListT e m
  stateE = ftMap stateE . stateErrorListCommute
instance (MonadState s m, Functorial Monoid m, Monoid s) => MonadState s (ErrorListT e m) where

-- }}}

-- State // Kon {{{

stateKonCommute :: StateT s (KonT (r, s) m) ~> KonT r (StateT s m)
stateKonCommute aSK = KonT $ \ (k :: a -> StateT s m r) -> StateT $ \ s ->
  runKonT (runStateT s aSK) $ \ (a, s') -> runStateT s' $ k a

konStateCommute :: KonT r (StateT s m) ~> StateT s (KonT (r, s) m)
konStateCommute aKS = StateT $ \ s -> KonT $ \ (k :: (a, s) -> m (r, s)) ->
  runStateT s $ runKonT aKS $ \ a -> StateT $ \ s' -> k (a, s')

instance (MonadState s m) => MonadStateI s (KonT r m) where
  stateI :: KonT r m ~> StateT s (KonT r m)
  stateI =
    mtMap (mtIsoMap stateE stateI)
    . mtMap stateKonCommute
    . stateI
    . konStateCommute
    . mtIsoMap stateI (stateE :: StateT s m ~> m)
instance (MonadState s m) => MonadStateE s (KonT r m) where
  stateE :: StateT s (KonT r m) ~> KonT r m
  stateE =
    mtIsoMap stateE stateI
    . stateKonCommute
    . stateE
    . mtMap konStateCommute
    . mtMap (mtIsoMap stateI (stateE :: StateT s m ~> m))

-- }}}

-- State // OpaqueKon {{{

instance (MonadState s m, FFIsomorphism (KFun r) (k r)) => MonadStateI s (OpaqueKonT k r m) where
  stateI :: OpaqueKonT k r m ~> StateT s (OpaqueKonT k r m)
  stateI =
    mtMap opaqueKonT
    . stateI
    . metaKonT
instance (MonadState s m, FFIsomorphism (KFun r) (k r)) => MonadStateE s (OpaqueKonT k r m) where
  stateE :: StateT s (OpaqueKonT k r m) ~> OpaqueKonT k r m
  stateE =
    opaqueKonT
    . stateE
    . mtMap metaKonT
instance (MonadState s m, FFIsomorphism (KFun r) (k r)) => MonadState s (OpaqueKonT k r m) where

-- }}}
