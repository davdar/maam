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
  
instance (Unit m) => Unit (MaybeT m) where unit = MaybeT . unit . Just
instance (Functor m) => Functor (MaybeT m) where map f = MaybeT . f ^^. unMaybeT
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
instance (Monad m) => Monad (MaybeT m)

instance FunctorUnit2 MaybeT where funit2 = MaybeT .^ Just
instance FunctorJoin2 MaybeT where
  fjoin2 = MaybeT . ff ^. unMaybeT . unMaybeT
    where
      ff Nothing = Nothing
      ff (Just aM) = aM
instance FunctorFunctor2 MaybeT where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> MaybeT m ~> MaybeT n
  fmap2 f = MaybeT . f . unMaybeT

instance (Functor m) => MonadMaybe (MaybeT m) where
  maybeI :: MaybeT m ~> MaybeT (MaybeT m)
  maybeI = maybeCommute . funit2
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
instance (Unit m, Functor m, Bind m) => Bind (ErrorT e m) where
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

instance (Functor m) => MonadError e (ErrorT e m) where
  errorI :: ErrorT e m ~> ErrorT e (ErrorT e m)
  errorI = errorCommute . funit2
  errorE :: ErrorT e (ErrorT e m) ~> ErrorT e m
  errorE = fjoin2 . errorCommute

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

instance (Functor m) => MonadReader r (ReaderT r m) where
  readerI :: ReaderT r m ~> ReaderT r (ReaderT r m)
  readerI = readerCommute . funit2
  readerE :: ReaderT r (ReaderT r m) ~> ReaderT r m
  readerE = fjoin2 . readerCommute

instance (MonadBot m) => MonadBot (ReaderT r m) where
  mbot = ReaderT $ const mbot
instance (MonadAppend m) => MonadAppend (ReaderT r m) where
  aM1 <++> aM2 = ReaderT $ \ r -> unReaderT aM1 r <++> unReaderT aM2 r

-- }}}

-- WriterT {{{

execWriterT :: (Functor m) => WriterT o m a -> m o
execWriterT = fst ^. unWriterT

mapOutput :: (Functor m) => (o1 -> o2) -> WriterT o1 m a -> WriterT o2 m a
mapOutput f = WriterT . mapFst f ^. unWriterT

writerCommute :: (Functor m) => WriterT o1 (WriterT o2 m) ~> WriterT o2 (WriterT o1 m)
writerCommute aMM = WriterT $ WriterT $ ff ^$ unWriterT $ unWriterT aMM
  where
    ff (o2, (o1, a)) = (o1, (o2, a))

instance (Unit m, Monoid o) => Unit (WriterT o m) where unit = WriterT . unit . (null,)
instance (Functor m) => Functor (WriterT o m) where map f = WriterT . mapSnd f ^. unWriterT
instance (Functor m, Product m, Monoid o) => Product (WriterT o m) where
  aM1 <*> aM2 = WriterT $ ff ^$ unWriterT aM1 <*> unWriterT aM2
    where
      ff ((o1, a1), (o2, a2)) = (o1 ++ o2, (a1, a2))
instance (Functor m, Applicative m, Monoid o) => Applicative (WriterT o m) where
  fM <@> aM = WriterT $ ff2 ^$ ff1 ^@ unWriterT fM <$> unWriterT aM
    where
      ff1 (o, f) = mapSnd ((o,) . f)
      ff2 (o2, (o1, a)) = (o1 ++ o2, a)
instance (Monad m, Monoid o) => Bind (WriterT o m) where
  aM >>= k = WriterT $ do
    (o1, a) <- unWriterT aM
    (o2, b) <- unWriterT $ k a
    return (o1 ++ o2, b)
instance (Monad m, Monoid o) => Monad (WriterT o m) where
instance (Monoid w) => FunctorUnit2 (WriterT w) where
  funit2 = WriterT .^ (null,)
instance FunctorJoin2 (WriterT w) where
  fjoin2 = snd ^. unWriterT
instance FunctorFunctor2 (WriterT w) where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> (WriterT w m ~> WriterT w n)
  fmap2 f aM = WriterT $ f $ unWriterT aM

instance (Functor m, Monoid o) => MonadWriter o (WriterT o m) where
  writerI :: WriterT o m ~> WriterT o (WriterT o m)
  writerI = writerCommute . funit2
  writerE :: WriterT o (WriterT o m) ~> WriterT o m
  writerE = fjoin2 . writerCommute

instance (MonadBot m, Monoid o) => MonadBot (WriterT o m) where
  mbot = WriterT $ mbot

-- }}}

-- StateT {{{ --

runStateT :: s -> StateT s m a -> m (s, a)
runStateT = flip unStateT

evalStateT :: (Functor m) => s -> StateT s m a -> m a
evalStateT = snd ^.: runStateT

execStateT :: (Functor m) => s -> StateT s m a -> m s
execStateT = fst ^.: runStateT

mapStateT :: (Functor m) => (s1 -> s2) -> (s2 -> s1) -> StateT s1 m a -> StateT s2 m a
mapStateT to from aM = StateT $ \ s2 -> ff ^$ unStateT aM $ from s2
  where ff (s1, a) = (to s1, a)

type State s = StateT s ID

runState :: s -> State s a -> (s, a)
runState = unID .: runStateT

evalState :: s -> State s a -> a
evalState = snd .: runState

execState :: s -> State s a -> s
execState = fst .: runState

stateCommute :: (Functor m) => StateT s1 (StateT s2 m) ~> StateT s2 (StateT s1 m)
stateCommute aMM = StateT $ \ s2 -> StateT $ \ s1 -> ff ^$ runStateT s2 $ runStateT s1 aMM
  where
    ff (s2, (s1, a)) = (s1, (s2, a))

stateLens :: (Functor m) => Lens s1 s2 -> StateT s2 m ~> StateT s1 m
stateLens l aM = StateT $ \ s1 ->
  let s2 = access l s1
      ff (s2', a) = (set l s2' s1, a)
  in ff ^$ unStateT aM s2

stateLensE :: (MonadState s1 m, Monad m) => Lens s1 s2 -> (StateT s2 m ~> m)
stateLensE = stateE .: stateLens

instance (Unit m) => Unit (StateT s m) where unit x = StateT $ \ s -> unit (s, x)
instance (Functor m) => Functor (StateT s m) where map f aM = StateT $ \ s -> mapSnd f ^$ unStateT aM s
instance (Monad m) => Product (StateT s m) where (<*>) = mpair
instance (Monad m) => Applicative (StateT s m) where (<@>) = mapply
instance (Monad m) => Bind (StateT s m) where
  aM >>= k = StateT $ \ s -> do
    (s', a) <- unStateT aM s
    unStateT (k a) s'
instance (Monad m) => Monad (StateT s m) where
instance FunctorUnit2 (StateT s) where funit2 aM = StateT $ \ s -> (s,) ^$ aM
instance FunctorJoin2 (StateT s) where fjoin2 aMM = StateT $ \ s -> runStateT s $ snd ^$ runStateT s aMM
instance FunctorFunctor2 (StateT s) where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> StateT s m ~> StateT s n
  fmap2 f aM = StateT $ f . unStateT aM

instance (MonadBot m) => MonadBot (StateT s m) where
  mbot = StateT $ const mbot
instance (MonadPlus m) => MonadPlus (StateT s m) where
  aM1 <+> aM2 = StateT $ \ s -> unStateT aM1 s <+> unStateT aM2 s
instance (MonadAppend m) => MonadAppend (StateT s m) where
  aM1 <++> aM2 = StateT $ \ s -> unStateT aM1 s <++> unStateT aM2 s

instance (Functorial Monoid m, Monoid s, Monoid a) => Monoid (StateT s m a) where
  null =
    with (functorial :: W (Monoid (m (s, a)))) $
    StateT $ \ _ -> null
  aM1 ++ aM2 =
    with (functorial :: W (Monoid (m (s, a)))) $
    StateT $ \ s -> unStateT aM1 s ++ unStateT aM2 s
instance (Functorial Monoid m, Monoid s) => Functorial Monoid (StateT s m) where
  functorial = W
instance (Functorial Bot m, Bot s, Bot a) => Bot (StateT s m a) where
  bot :: StateT s m a
  bot = 
    with (functorial :: W (Bot (m (s, a)))) $
    StateT $ \ _ -> bot
instance (Functorial Join m, Join s, Join a) => Join (StateT s m a) where
  aM1 \/ aM2 = 
    with (functorial :: W (Join (m (s, a)))) $
    StateT $ \ s -> unStateT aM1 s \/ unStateT aM2 s
instance (Functorial Bot m, Functorial Join m, JoinLattice s, JoinLattice a) => JoinLattice (StateT s m a)
instance (Functorial Bot m, Functorial Join m, JoinLattice s) => Functorial JoinLattice (StateT s m) where functorial = W

instance (Functor m) => MonadState s (StateT s m) where
  stateI :: StateT s m ~> StateT s (StateT s m) 
  stateI = stateCommute . funit2
  stateE :: StateT s (StateT s m) ~> StateT s m
  stateE = fjoin2 . stateCommute

-- }}} --

-- AddStateT {{{

newtype AddStateT s12 s1 m a = AddStateT { runAddStateT :: StateT s1 m a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadBot, MonadPlus, MonadAppend
    , MonadReader r
    , MonadWriter o
    )

mergeState :: (Functor m) => StateT s1 (StateT s2 m) a -> StateT (s1, s2) m a
mergeState aMM = StateT $ \ (s1, s2) -> ff ^$ unStateT (unStateT aMM s1) s2
  where
    ff (s2, (s1, a)) = ((s1, s2), a)

splitState :: (Functor m) => StateT (s1, s2) m a -> StateT s1 (StateT s2 m) a
splitState aM = StateT $ \ s1 -> StateT $ \ s2 -> ff ^$ unStateT aM (s1, s2)
  where
    ff ((s1, s2), a) = (s2, (s1, a))

instance (Functor m, MonadState s2 m, Isomorphism s12 (s1, s2)) => MonadState s12 (AddStateT s12 s1 m) where
  stateI :: AddStateT s12 s1 m ~> StateT s12 (AddStateT s12 s1 m)
  stateI = 
    fmap2 AddStateT
    . mapStateT isofrom isoto
    . mergeState
    . fmap2 (stateCommute . fmap2 stateI)
    . stateI
    . runAddStateT
  stateE :: StateT s12 (AddStateT s12 s1 m) ~> AddStateT s12 s1 m
  stateE = 
    AddStateT
    . stateE
    . fmap2 (fmap2 stateE . stateCommute) 
    . splitState
    . mapStateT isoto isofrom
    . fmap2 runAddStateT

-- }}}

-- RWST {{{

runRWST :: (Functor m) => r -> s -> RWST r o s m a -> m (s, o, a)
runRWST r0 s0 = ff ^. runStateT s0 . unWriterT . runReaderT r0 . unRWST
  where
    ff (s, (o, a)) = (s, o, a)
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

deriving instance (Monad m, Monoid o) => MonadReader r (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadWriter o (RWST r o s m)
deriving instance (Monad m, Monoid o) => MonadState s (RWST r o s m)
instance (Monad m, Monoid o) => MonadRWS r o s (RWST r o s m) where
  rwsI :: RWST r o s m ~> RWST r o s (RWST r o s m)
  rwsI = rwsCommute . munit2
  rwsE :: RWST r o s (RWST r o s m) ~> RWST r o s m
  rwsE = mjoin2 . rwsCommute

deriving instance (MonadBot m, Monoid o) => MonadBot (RWST r o s m)
deriving instance (Functor m, MonadMaybe m, Monoid o) => MonadMaybe (RWST r o s m)

-- }}}

-- ListT {{{

newtype ListT m a = ListT { unListT :: m [a] }
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
instance (Monad m, Functorial Monoid m) => Bind (ListT m) where
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
instance (Functorial Monoid m) => MonadBot (ListT m) where
  mbot =  null
instance (Functorial Monoid m) => MonadAppend (ListT m) where
  (<++>) = (++)

maybeToList :: (Functor m) => MaybeT m a -> ListT m a
maybeToList aM = ListT $ ff ^$ unMaybeT aM
  where
    ff Nothing = []
    ff (Just a) = [a]

-- }}}

-- ListSetT {{{

newtype ListSetT m a = ListSetT { unListSetT :: m (ListSet a) }
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
instance (Monad m, Functorial JoinLattice m) => Bind (ListSetT m) where
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

instance (Functorial JoinLattice m) => MonadBot (ListSetT m) where
  mbot :: forall a. ListSetT m a
  mbot = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT bot
instance (Functorial JoinLattice m) => MonadPlus (ListSetT m) where
  (<+>) :: forall a. ListSetT m a -> ListSetT m a -> ListSetT m a
  aM1 <+> aM2 = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT $ unListSetT aM1 \/ unListSetT aM2

-- }}}

-- SetT {{{

newtype SetT m a = SetT { unSetT :: m (Set a) }
mapSetT :: (m (Set a) -> m (Set b)) -> SetT m a -> SetT m b
mapSetT f = SetT . f . unSetT

setCommute :: (Functor m) => SetT (SetT m) ~> SetT (SetT m)
setCommute = SetT . SetT . setTranspose ^. unSetT . unSetT

instance (Functor m, Product m) => Product (SetT m) where
  (<*>) :: forall a b. SetT m a -> SetT m b -> SetT m (a, b)
  aM1 <*> aM2 = SetT $ uncurry (<*>) ^$ unSetT aM1 <*> unSetT aM2
instance (Functorial JoinLattice m, Monad m) => Bind (SetT m) where
  aM >>= k = SetT $ do
    aC <- unSetT aM
    unSetT $ msum $ k ^$ toList aC
instance (Functorial JoinLattice m) => MonadBot (SetT m) where
  mbot :: forall a. SetT m a
  mbot = 
    with (functorial :: W (JoinLattice (m (Set a)))) $
    SetT bot
instance (Functorial JoinLattice m) => MonadPlus (SetT m) where
  (<+>) :: forall a. SetT m a -> SetT m a -> SetT m a
  aM1 <+> aM2 =
    with (functorial :: W (JoinLattice (m (Set a)))) $
    SetT $ unSetT aM1 \/ unSetT aM2

-- }}}

-- ContT {{{

evalKonT :: (Unit m) => ContT r m r -> m r
evalKonT aM = unContT aM unit

type Kon r = ContT r ID
runKon :: Kon r a -> (a -> r) -> r
runKon aM f = unID $ unContT aM (ID . f)
evalKon :: Kon r r -> r
evalKon aM = runKon aM id

instance (Unit m) => Unit (ContT r m) where
  unit a = ContT $ \ k -> k a
instance (Unit m) => Applicative (ContT r m) where
  (<@>) = mapply
instance (Unit m) => Product (ContT r m) where
  (<*>) = mpair
instance (Unit m) => Functor (ContT r m) where
  map = mmap
instance (Unit m) => Bind (ContT r m) where
  (>>=) :: ContT r m a -> (a -> ContT r m b) -> ContT r m b
  aM >>= kM = ContT $ \ (k :: b -> m r) -> unContT aM $ \ a -> unContT (kM a) k
instance (Unit m) => Monad (ContT r m) where
instance MonadIsoFunctor2 (ContT r) where
  misoMap2 :: (Monad m, Monad n) => (m ~> n, n ~> m) -> (ContT r m ~> ContT r n)
  misoMap2 (to, from) aM = ContT $ \ (k :: a -> n r) -> to $ unContT aM $ \ a -> from $ k a

instance (Monad m) => MonadCont r (ContT r m) where
  contI :: ContT r m ~> ContT r (ContT r m)
  contI aM = ContT $ \ (k1 :: a -> ContT r m r) -> ContT $ \ (k2 :: r -> m r) ->
    k2 *$ unContT aM $ \ a -> unContT (k1 a) return
  contE :: ContT r (ContT r m) ~> ContT r m
  contE aMM = ContT $ \ (k :: a -> m r) -> 
    let aM :: ContT r m r
        aM = unContT aMM $ \ a -> ContT $ \ (k' :: r -> m r) -> k' *$ k a
    in unContT aM return

-- }}}

-- OpaqueContT {{{

newtype ContFun r m a = ContFun { unContFun :: a -> m r }
type OpaqueKon k r = OpaqueContT k r ID

runOpaqueKonTWith :: k r m a -> OpaqueContT k r m a -> m r
runOpaqueKonTWith = flip unOpaqueContT
makeMetaKonT :: (Morphism3 (k r) (ContFun r)) => ((a -> m r) -> m r) -> OpaqueContT k r m a
makeMetaKonT nk = OpaqueContT $ \ (k :: k r m a) -> nk $ unContFun $ morph3 k
runMetaKonT :: (Morphism3 (ContFun r) (k r)) => OpaqueContT k r m a -> (a -> m r) -> m r
runMetaKonT aM k = unOpaqueContT aM $ morph3 $ ContFun k
runMetaKonTWith :: (Morphism3 (ContFun r) (k r)) => (a -> m r) -> OpaqueContT k r m a -> m r
runMetaKonTWith = flip runMetaKonT
evalOpaqueKonT :: (Unit m, Morphism3 (ContFun r) (k r)) => OpaqueContT k r m r -> m r
evalOpaqueKonT aM = runMetaKonT aM unit

makeOpaqueKon :: (k r ID a -> r) -> OpaqueKon k r a
makeOpaqueKon nk = OpaqueContT $ ID . nk
makeMetaKon :: (Morphism3 (k r) (ContFun r)) => ((a -> r) -> r) -> OpaqueKon k r a
makeMetaKon nk = makeOpaqueKon $ \ (k :: k r ID a) -> nk $ (.) unID . unContFun $ morph3 k
runOpaqueKon :: OpaqueKon k r a -> k r ID a -> r
runOpaqueKon = unID .: unOpaqueContT
runMetaKon :: (Morphism3 (ContFun r) (k r)) => OpaqueKon k r a -> (a -> r) -> r
runMetaKon aM k = runOpaqueKon aM $ morph3 $ ContFun $ ID . k
evalOpaqueKon :: (Morphism3 (ContFun r) (k r)) => OpaqueKon k r r -> r
evalOpaqueKon aM = runMetaKon aM id

metaKonT :: (Morphism3 (ContFun r) (k r)) => OpaqueContT k r m ~> ContT r m
metaKonT aM = ContT $ \ (k :: a -> m r) -> runMetaKonT aM k

opaqueContT :: (Morphism3 (k r) (ContFun r)) => ContT r m ~> OpaqueContT k r m
opaqueContT aM = makeMetaKonT $ \ (k :: a -> m r) -> unContT aM k

instance (Morphism3 (k r) (ContFun r)) => Unit (OpaqueContT k r m) where
  unit :: a -> OpaqueContT k r m a
  unit a = OpaqueContT  $ \ k -> unContFun (morph3 k) a
instance (Monad m, Isomorphism3 (ContFun r) (k r)) => Functor (OpaqueContT k r m) where map = mmap
instance (Monad m, Isomorphism3 (ContFun r) (k r)) => Applicative (OpaqueContT k r m) where (<@>) = mapply
instance (Monad m, Isomorphism3 (ContFun r) (k r)) => Product (OpaqueContT k r m) where (<*>) = mpair
instance (Monad m, Isomorphism3 (ContFun r) (k r)) => Bind (OpaqueContT k r m) where
  (>>=) :: OpaqueContT k r m a -> (a -> OpaqueContT k r m b) -> OpaqueContT k r m b
  aM >>= kM = OpaqueContT $ \ (k :: k r m a) -> runMetaKonT aM $ \ a -> unOpaqueContT (kM a) k
instance (Monad m, Isomorphism3 (ContFun r) (k r)) => Monad (OpaqueContT k r m) where
instance (Isomorphism3 (k r) (ContFun r)) => MonadIsoFunctor2 (OpaqueContT k r) where
  misoMap2 :: (Monad m, Monad n) => (m ~> n, n ~> m) -> OpaqueContT k r m ~> OpaqueContT k r n
  misoMap2 tofrom = opaqueContT . misoMap2 tofrom . metaKonT

class Balloon k r | k -> r where
  inflate :: (Monad m) => k r m ~> k r (OpaqueContT k r m)
  deflate :: (Monad m) => k r (OpaqueContT k r m) ~> k r m
instance (Monad m, Isomorphism3 (ContFun r) (k r), Balloon k r) => MonadOpaqueCont k r (OpaqueContT k r m) where
  opaqueContI :: OpaqueContT k r m a -> OpaqueContT k r (OpaqueContT k r m) a
  opaqueContI aM = OpaqueContT $ \ k1 -> makeMetaKonT $ \ (k2 :: r -> m r) -> k2 *$ unOpaqueContT aM $ deflate k1
  opaqueContE :: OpaqueContT k r (OpaqueContT k r m) a -> OpaqueContT k r m a
  opaqueContE kk = OpaqueContT $ \ (k :: k r m a ) -> runMetaKonTWith return $ unOpaqueContT kk $ inflate k

instance (Monad m, Isomorphism3 (ContFun r) (k r)) => MonadCont r (OpaqueContT k r m) where
  contI :: OpaqueContT k r m ~> ContT r (OpaqueContT k r m)
  contI aM = ContT $ \ (k1 :: a -> OpaqueContT k r m r) -> makeMetaKonT $ \ (k2 :: r -> m r) ->
    k2 *$ runMetaKonT aM $ \ a -> runMetaKonT (k1 a) return
  contE :: ContT r (OpaqueContT k r m) ~> OpaqueContT k r m
  contE aMM = makeMetaKonT $ \ (k :: a -> m r) ->
    runMetaKonTWith return $ unContT aMM $ \ a -> makeMetaKonT $ \ (k' :: r -> m r) -> k' *$ k a

-- }}}

----------------------
-- Monads Commuting --
----------------------

-- Maybe // * --

-- Maybe // Reader // FULL COMMUTE {{{

maybeReaderCommute :: (Functor m) => MaybeT (ReaderT r m) ~> ReaderT r (MaybeT m)
maybeReaderCommute aMRM = ReaderT $ \ r -> MaybeT $ runReaderT r $ unMaybeT aMRM

readerMaybeCommute :: (Functor m) => ReaderT r (MaybeT m) ~> MaybeT (ReaderT r m)
readerMaybeCommute aRMM = MaybeT $ ReaderT $ \ r -> unMaybeT $ runReaderT r aRMM

instance (Functor m, MonadReader r m) => MonadReader r (MaybeT m) where
  readerI :: MaybeT m ~> ReaderT r (MaybeT m)
  readerI = maybeReaderCommute . fmap2 readerI
  readerE :: ReaderT r (MaybeT m) ~> MaybeT m
  readerE = fmap2 readerE . readerMaybeCommute

instance (Functor m, MonadMaybe m) => MonadMaybe (ReaderT r m) where
  maybeI :: ReaderT r m ~> MaybeT (ReaderT r m)
  maybeI = readerMaybeCommute . fmap2 maybeI
  maybeE :: MaybeT (ReaderT r m) ~> ReaderT r m
  maybeE = fmap2 maybeE . maybeReaderCommute

-- }}}

-- Maybe // Writer {{{

writerMaybeCommute :: (Monoid w, Functor m) => WriterT w (MaybeT m) ~> MaybeT (WriterT w m)
writerMaybeCommute aRMM = MaybeT $ WriterT $ ff ^$ unMaybeT $ unWriterT aRMM
  where
    ff Nothing = (null, Nothing)
    ff (Just (w, a)) = (w, Just a)

maybeWriterCommute :: (Functor m) => MaybeT (WriterT w m) ~> WriterT w (MaybeT m)
maybeWriterCommute aMRM = WriterT $ MaybeT $ ff ^$ unWriterT $ unMaybeT aMRM
  where
    ff (_, Nothing) = Nothing
    ff (w, Just a) = Just (w, a)

instance (Monoid w, Functor m, MonadWriter w m) => MonadWriter w (MaybeT m) where
  writerI :: MaybeT m ~> WriterT w (MaybeT m)
  writerI = maybeWriterCommute . fmap2 writerI
  writerE :: WriterT w (MaybeT m) ~> MaybeT m
  writerE = fmap2 writerE . writerMaybeCommute

instance (Monoid w, Functor m, MonadMaybe m) => MonadMaybe (WriterT w m) where
  maybeI :: WriterT w m ~> MaybeT (WriterT w m)
  maybeI = writerMaybeCommute . fmap2 maybeI
  maybeE :: MaybeT (WriterT w m) ~> WriterT w m
  maybeE = fmap2 maybeE . maybeWriterCommute

-- }}}

-- Maybe // State {{{

maybeStateCommute :: (Functor m) => MaybeT (StateT s m) ~> StateT s (MaybeT m)
maybeStateCommute aMSM = StateT $ \ s1 -> MaybeT $ ff ^$ runStateT s1 $ unMaybeT aMSM
  where
    ff (_, Nothing) = Nothing
    ff (s2, Just a) = Just (s2, a)

stateMaybeCommute :: (Functor m) => StateT s (MaybeT m) ~> MaybeT (StateT s m)
stateMaybeCommute aSMM = MaybeT $ StateT $ \ s1 -> ff s1 ^$ unMaybeT $ runStateT s1 aSMM
  where
    ff s1 Nothing = (s1, Nothing)
    ff _ (Just (s2, a)) = (s2, Just a)

instance (Functor m, MonadState s m) => MonadState s (MaybeT m) where
  stateI :: MaybeT m ~> StateT s (MaybeT m)
  stateI = maybeStateCommute . fmap2 stateI
  stateE :: StateT s (MaybeT m) ~> MaybeT m
  stateE = fmap2 stateE . stateMaybeCommute

instance (Functor m, MonadMaybe m) => MonadMaybe (StateT s m) where
  maybeI :: StateT s m ~> MaybeT (StateT s m)
  maybeI = stateMaybeCommute . fmap2 maybeI
  maybeE :: MaybeT (StateT s m) ~> StateT s m
  maybeE = fmap2 maybeE . maybeStateCommute

-- }}}

-- Error // * --

-- Error // Reader {{{

errorReaderCommute :: ErrorT e (ReaderT r m) ~> ReaderT r (ErrorT e m)
errorReaderCommute aMRM = ReaderT $ \ r -> ErrorT $ runReaderT r $ unErrorT aMRM

readerErrorCommute :: ReaderT r (ErrorT e m) ~> ErrorT e (ReaderT r m)
readerErrorCommute aRMM = ErrorT $ ReaderT $ \ r -> unErrorT $ runReaderT r aRMM

instance (Functor m, MonadReader r m) => MonadReader r (ErrorT e m) where
  readerI :: ErrorT e m ~> ReaderT r (ErrorT e m)
  readerI = errorReaderCommute . fmap2 readerI
  readerE :: ReaderT r (ErrorT e m) ~> ErrorT e m
  readerE = fmap2 readerE . readerErrorCommute

instance (Functor m, MonadError e m) => MonadError e (ReaderT r m) where
  errorI :: ReaderT r m ~> ErrorT e (ReaderT r m)
  errorI = readerErrorCommute . fmap2 errorI
  errorE :: ErrorT e (ReaderT r m) ~> ReaderT r m
  errorE = fmap2 errorE . errorReaderCommute

-- }}}

-- Error // State {{{

errorStateCommute :: (Functor m) => ErrorT e (StateT s m) ~> StateT s (ErrorT e m)
errorStateCommute aMRM = StateT $ \ s -> ErrorT $ ff ^$ runStateT s $ unErrorT aMRM
  where
    ff (_, Inl e) = Inl e
    ff (s, Inr a) = Inr (s, a)

stateErrorCommute :: (Functor m) => StateT s (ErrorT e m) ~> ErrorT e (StateT s m)
stateErrorCommute aRMM = ErrorT $ StateT $ \ s -> ff s ^$ unErrorT $ runStateT s aRMM
  where
    ff s (Inl e) = (s, Inl e)
    ff _ (Inr (s, a)) = (s, Inr a)

instance (Functor m, MonadState s m) => MonadState s (ErrorT e m) where
  stateI :: ErrorT e m ~> StateT s (ErrorT e m)
  stateI = errorStateCommute . fmap2 stateI
  stateE :: StateT s (ErrorT e m) ~> ErrorT e m
  stateE = fmap2 stateE . stateErrorCommute

instance (Functor m, MonadError e m) => MonadError e (StateT s m) where
  errorI :: StateT s m ~> ErrorT e (StateT s m)
  errorI = stateErrorCommute . fmap2 errorI
  errorE :: ErrorT e (StateT s m) ~> StateT s m
  errorE = fmap2 errorE . errorStateCommute

-- }}}

-- Reader // * --

-- Reader // Writer // FULL COMMUTE {{{

readerWriterCommute :: ReaderT r (WriterT w m) ~> WriterT w (ReaderT r m)
readerWriterCommute aRWM = WriterT $ ReaderT $ \ r -> unWriterT $ runReaderT r aRWM

writerReaderCommute :: WriterT w (ReaderT r m) ~> ReaderT r (WriterT w m)
writerReaderCommute aWRM = ReaderT $ \ r -> WriterT $ runReaderT r $ unWriterT aWRM

instance (Monoid w, Functor m, MonadWriter w m) => MonadWriter w (ReaderT r m) where
  writerI :: ReaderT r m ~> WriterT w (ReaderT r m)
  writerI = readerWriterCommute . fmap2 writerI
  writerE :: WriterT w (ReaderT r m) ~> ReaderT r m
  writerE = fmap2 writerE . writerReaderCommute

instance (Monoid w, Functor m, MonadReader r m) => MonadReader r (WriterT w m) where
  readerI :: WriterT w m ~> ReaderT r (WriterT w m)
  readerI = writerReaderCommute . fmap2 readerI
  readerE :: ReaderT r (WriterT w m) ~> WriterT w m
  readerE = fmap2 readerE . readerWriterCommute

-- }}}

-- Reader // State // FULL COMMUTE {{{

readerStateCommute :: (Functor m) => ReaderT r (StateT s m) ~> StateT s (ReaderT r m)
readerStateCommute aRSM = StateT $ \ s -> ReaderT $ \ r ->
  runStateT s $ runReaderT r aRSM

stateReaderCommute :: (Functor m) => StateT s (ReaderT r m) ~> ReaderT r (StateT s m)
stateReaderCommute aSRM = ReaderT $ \ r -> StateT $ \ s -> 
  runReaderT r $ runStateT s aSRM

instance (Functor m, MonadState s m) => MonadState s (ReaderT r m) where
  stateI :: ReaderT r m ~> StateT s (ReaderT r m)
  stateI = readerStateCommute . fmap2 stateI
  stateE :: StateT s (ReaderT r m) ~> ReaderT r m
  stateE = fmap2 stateE . stateReaderCommute

instance (Functor m, MonadReader r m) => MonadReader r (StateT s m) where
  readerI :: StateT s m ~> ReaderT r (StateT s m)
  readerI = stateReaderCommute . fmap2 readerI
  readerE :: ReaderT r (StateT s m) ~> StateT s m
  readerE = fmap2 readerE . readerStateCommute

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
    ff (s, (w, a)) = (w, (s, a))

stateWriterCommute :: (Functor m) => StateT s (WriterT w m) ~> WriterT w (StateT s m)
stateWriterCommute aMRM = WriterT $ StateT $ ff ^. unWriterT . unStateT aMRM
  where
    ff (w, (s, a)) = (s, (w, a))

instance (Functor m, Monoid w, MonadState s m) => MonadState s (WriterT w m) where
  stateI :: WriterT w m ~> StateT s (WriterT w m)
  stateI = writerStateCommute . fmap2 stateI
  stateE :: StateT s (WriterT w m) ~> WriterT w m
  stateE = fmap2 stateE . stateWriterCommute

instance (Monoid w, Functor m, MonadWriter w m) => MonadWriter w (StateT s m) where
  writerI :: StateT s m ~> WriterT w (StateT s m)
  writerI = stateWriterCommute . fmap2 writerI
  writerE :: WriterT w (StateT s m) ~> StateT s m
  writerE = fmap2 writerE . writerStateCommute

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
    ff asL = (concat $ fst ^$ asL, snd ^$ asL)

listStateCommute :: (Functor m) => ListT (StateT s m) ~> StateT s (ListT m)
listStateCommute aMM = StateT $ \ s -> ListT $ ff ^$ runStateT s $ unListT aMM
  where
    ff (s, xs) = (s,) ^$ xs

instance (Functor m, MonadState s m, Functorial Monoid m, Monoid s) => MonadState s (ListT m) where
  stateI :: ListT m ~> StateT s (ListT m)
  stateI = listStateCommute . fmap2 stateI
  stateE :: StateT s (ListT m) ~> ListT m
  stateE = fmap2 stateE . stateListCommute

-- }}}

-- State // ListSet {{{

stateListSetCommute :: (Functor m, JoinLattice s) => StateT s (ListSetT m) ~> ListSetT (StateT s m)
stateListSetCommute aMM = ListSetT $ StateT $ \ s -> ff ^$ unListSetT $ runStateT s aMM
  where
    ff asL = (joins $ fst ^$ asL, snd ^$ asL)

listSetStateCommute :: (Functor m) => ListSetT (StateT s m) ~> StateT s (ListSetT m)
listSetStateCommute aMM = StateT $ \ s -> ListSetT $ ff ^$ runStateT s $ unListSetT aMM
  where
    ff (s, xs) = (s,) ^$ xs

instance (Functor m, MonadState s m, Functorial JoinLattice m, JoinLattice s) => MonadState s (ListSetT m) where
  stateI :: ListSetT m ~> StateT s (ListSetT m)
  stateI = listSetStateCommute . fmap2 stateI
  stateE :: StateT s (ListSetT m) ~> ListSetT m
  stateE = fmap2 stateE . stateListSetCommute

-- }}}

-- State // Kon {{{

stateKonCommute :: StateT s (ContT (s, r) m) ~> ContT r (StateT s m)
stateKonCommute aSK = ContT $ \ (k :: a -> StateT s m r) -> StateT $ \ s ->
  unContT (runStateT s aSK) $ \ (s', a) -> runStateT s' $ k a

konStateCommute :: ContT r (StateT s m) ~> StateT s (ContT (s, r) m)
konStateCommute aKS = StateT $ \ s -> ContT $ \ (k :: (s, a) -> m (s, r)) ->
  runStateT s $ unContT aKS $ \ a -> StateT $ \ s' -> k (s',a)

instance (Monad m, MonadState s m) => MonadState s (ContT r m) where
  stateI :: ContT r m ~> StateT s (ContT r m)
  stateI =
    fmap2 (misoMap2 (stateE, stateI))
    . fmap2 stateKonCommute
    . stateI
    . konStateCommute
    . misoMap2 (stateI, stateE :: StateT s m ~> m)
  stateE :: StateT s (ContT r m) ~> ContT r m
  stateE =
    misoMap2 (stateE, stateI)
    . stateKonCommute
    . stateE
    . fmap2 konStateCommute
    . fmap2 (misoMap2 (stateI, stateE :: StateT s m ~> m))

-- }}}

-- State // OpaqueKon {{{

instance (Monad m, MonadState s m, Isomorphism3 (ContFun r) (k r)) => MonadState s (OpaqueContT k r m) where
  stateI :: OpaqueContT k r m ~> StateT s (OpaqueContT k r m)
  stateI =
    fmap2 opaqueContT
    . stateI
    . metaKonT
  stateE :: StateT s (OpaqueContT k r m) ~> OpaqueContT k r m
  stateE =
    opaqueContT
    . stateE
    . fmap2 metaKonT

-- }}}
