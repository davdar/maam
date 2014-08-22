module FP.Monads where

import FP.Core

infixr 9 :@:

-- Transformer Zipper {{{

newtype (t :@: m) a = Trans { runTrans :: t m a }

mtBegin :: m ~> IDT :@: m
mtBegin aM = Trans $ IDT aM

mtEnd :: IDT :@: m ~> m
mtEnd aM = runIDT $ runTrans aM

mtPush :: t1 :@: t2 m ~> (t1 :..: t2) :@: m
mtPush aM = Trans $ Compose2 $ runTrans aM

mtPop :: (t1 :..: t2) :@: m ~> t1 :@: t2 m
mtPop aM = Trans $ runCompose2 $ runTrans aM

mtzMap :: (MonadFunctor t) => (m ~> n) -> t :@: m ~> t :@: n
mtzMap f aM = Trans $ mtMap f $ runTrans aM

-- }}}

-- ID {{{

newtype ID a = ID { runID :: a }
  deriving
  ( Eq, Ord
  , PartialOrder
  , HasBot
  , JoinLattice
  )

instance Unit ID where
  unit = ID
instance Functor ID where
  map f = ID . f . runID
instance FunctorM ID where
  mapM f = map ID . f . runID
instance CFunctor Universal ID where
  cmap = map
instance CFunctorM Universal ID where
  cmapM = mapM
instance Applicative ID where
  aM <*> bM = ID $ (runID aM, runID bM)
instance Monad ID where
  aM >>= k = k $ runID aM
instance Functorial HasBot ID where
  functorial = W
instance Functorial JoinLattice ID where
  functorial = W

newtype IDT m a = IDT { runIDT :: m a }

-- }}}

-- ReaderT {{{

readerCommute :: ReaderT r1 (ReaderT r2 m) ~> ReaderT r2 (ReaderT r1 m)
readerCommute aMM = ReaderT $ \ r2 -> ReaderT $ \ r1 -> runReaderT r2 $ runReaderT r1 aMM

instance (Unit m) => Unit (ReaderT r m) where
  unit = ReaderT . const . unit
instance (Functor m) => Functor (ReaderT r m) where
  map f = ReaderT . map (map f) . unReaderT
instance (Applicative m) => Applicative (ReaderT r m) where
  aM1 <*> aM2 = ReaderT $ \ r ->
    runReaderT r aM1 <*> runReaderT r aM2
instance (Monad m) => Monad (ReaderT r m) where
  aM >>= k = ReaderT $ \ r -> do
    a <- runReaderT r aM
    runReaderT r $ k a
instance MonadUnit (ReaderT r) where
  mtUnit = ReaderT . const
instance MonadCounit (ReaderT r) where
  mtCounit aMM = ReaderT $ \ r -> runReaderT r $ runReaderT r aMM
instance MonadFunctor (ReaderT r) where
  mtMap :: (m ~> n) -> (ReaderT r m ~> ReaderT r n)
  mtMap f aM = ReaderT $ \ r -> f $ runReaderT r aM

instance (Monad m) => MonadReaderI r (ReaderT r m) where
  readerI :: ReaderT r m ~> ReaderT r (ReaderT r m)
  readerI = readerCommute . mtUnit
instance (Monad m) => MonadReaderE r (ReaderT r m) where
  readerE :: ReaderT r (ReaderT r m) ~> ReaderT r m
  readerE = mtCounit . readerCommute
instance (Monad m) => MonadReader r (ReaderT r m) where

instance (MonadZero m) => MonadZero (ReaderT r m) where
  mzero = ReaderT $ const mzero

-- }}}

-- WriterT {{{

writerCommute :: (Functor m) => WriterT o1 (WriterT o2 m) ~> WriterT o2 (WriterT o1 m)
writerCommute aMM = WriterT $ WriterT $ map ff $ runWriterT $ runWriterT aMM
  where
    ff ((a, o1), o2) = ((a, o2), o1)

instance (Unit m, Monoid o) => Unit (WriterT o m) where
  unit = WriterT . unit . (,null)
instance (Functor m) => Functor (WriterT o m) where
  map f = WriterT . map (mapFst f) . runWriterT
instance (Applicative m, Monoid o) => Applicative (WriterT o m) where
  aM1 <*> aM2 = WriterT $
    map (\ ((a1, o1), (a2, o2)) -> ((a1, a2), (o1 ++ o2))) $
      runWriterT aM1 <*> runWriterT aM2
instance (Monad m, Monoid o) => Monad (WriterT o m) where
  aM >>= k = WriterT $ do
    (a, o1) <- runWriterT aM
    (b, o2) <- runWriterT $ k a
    return (b, o1 ++ o2)
instance (Monoid w) => MonadUnit (WriterT w) where
  mtUnit = WriterT . map (,null)
-- this also exists for (WriterT w m ~> m)
instance MonadCounit (WriterT w) where
  mtCounit = map fst . runWriterT
instance MonadFunctor (WriterT w) where
  mtMap :: (m ~> n) -> (WriterT w m ~> WriterT w n)
  mtMap f aM = WriterT $ f $ runWriterT aM

instance (Monad m, Monoid o) => MonadWriterI o (WriterT o m) where
  writerI :: WriterT o m ~> WriterT o (WriterT o m)
  writerI = writerCommute . mtUnit
instance (Monad m, Monoid o) => MonadWriterE o (WriterT o m) where
  writerE :: WriterT o (WriterT o m) ~> WriterT o m
  writerE = mtCounit . writerCommute
instance (Monad m, Monoid o) => MonadWriter o (WriterT o m) where

instance (MonadZero m, Monoid o) => MonadZero (WriterT o m) where
  mzero = WriterT $ mzero

-- }}}

-- StateT {{{ --

runStateT :: s -> StateT s m a -> m (a, s)
runStateT = flip unStateT

evalStateT :: (Functor m) => s -> StateT s m a -> m a
evalStateT = map fst .: runStateT

execStateT :: (Functor m) => s -> StateT s m a -> m s
execStateT = map snd .: runStateT

type State s = StateT s ID

runState :: s -> State s a -> (a, s)
runState = runID .: runStateT

evalState :: s -> State s a -> a
evalState = fst .: runState

execState :: s -> State s a -> s
execState = snd .: runState

stateCommute :: (Functor m) => StateT s1 (StateT s2 m) ~> StateT s2 (StateT s1 m)
stateCommute aMM = StateT $ \ s2 -> StateT $ \ s1 -> map ff $ runStateT s2 $ runStateT s1 aMM
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
  map f aM = StateT $ \ s -> map (mapFst f) (unStateT aM s)
instance (Monad m) => Applicative (StateT s m) where
  (<*>) = mpair
instance (Monad m) => Monad (StateT s m) where
  aM >>= k = StateT $ \ s -> do
    (a, s') <- unStateT aM s
    unStateT (k a) s'
instance MonadUnit (StateT s) where
  mtUnit aM = StateT $ \ s -> map (,s) aM
instance MonadCounit (StateT s) where
  mtCounit aMM = StateT $ \ s -> runStateT s $ fst <$> runStateT s aMM
instance MonadFunctor (StateT s) where
  mtMap :: (m ~> n) -> StateT s m ~> StateT s n
  mtMap f aM = StateT $ f . unStateT aM

instance (Monad m) => MonadStateI s (StateT s m) where
  stateI :: StateT s m ~> StateT s (StateT s m) 
  stateI = stateCommute . mtUnit
instance (Monad m) => MonadStateE s (StateT s m) where
  stateE :: StateT s (StateT s m) ~> StateT s m
  stateE = mtCounit . stateCommute
instance (Monad m) => MonadState s (StateT s m) where

instance (MonadZero m) => MonadZero (StateT s m) where
  mzero = StateT $ const mzero
instance (MonadPlus m) => MonadPlus (StateT s m) where
  aM1 <+> aM2 = StateT $ \ s -> unStateT aM1 s <+> unStateT aM2 s

instance (Functorial HasBot m, HasBot s, HasBot a) => HasBot (StateT s m a) where
  bot :: StateT s m a
  bot = 
    with (functorial :: W (HasBot (m (a, s)))) $
    StateT $ \ _ -> bot
instance (Functorial HasBot m, Functorial JoinLattice m, JoinLattice s, JoinLattice a) => JoinLattice (StateT s m a) where
  aM1 \/ aM2 = 
    with (functorial :: W (JoinLattice (m (a, s)))) $
    StateT $ \ s -> unStateT aM1 s \/ unStateT aM2 s
instance (Functorial HasBot m, Functorial JoinLattice m, JoinLattice s) => Functorial JoinLattice (StateT s m) where
  functorial = W

-- }}} --

-- RWST {{{

runRWST :: (Functor m) => r -> s -> RWST r o s m a -> m (a, o, s)
runRWST r0 s0 = map ff . runStateT s0 . runWriterT . runReaderT r0 . unRWST
  where
    ff ((a, o), s) = (a, o, s)
rwsCommute :: (Functor m, Monoid o1) => RWST r1 o1 s1 (RWST r2 o2 s2 m) ~> RWST r2 o2 s2 (RWST r1 o1 s1 m)
rwsCommute =
  RWST
  . mtMap (mtMap rwsStateCommute . rwsWriterCommute)
  . rwsReaderCommute
  . mtMap unRWST

deriving instance (Unit m, Monoid o) => Unit (RWST r o s m)
deriving instance (Functor m) => Functor (RWST r o s m)
deriving instance (Monad m, Monoid o) => Applicative (RWST r o s m)
deriving instance (Monad m, Monoid o) => Monad (RWST r o s m)
instance (Monoid o) => MonadUnit (RWST r o s) where
  mtUnit = RWST . mtUnit . mtUnit . mtUnit
instance (Monoid o) => MonadCounit (RWST r o s) where
  mtCounit =
    RWST
    . mtCounit
    . mtMap (mtMap mtCounit . writerReaderCommute)
    . mtMap (mtMap (mtMap (mtMap mtCounit . stateWriterCommute) . stateReaderCommute))
    . unRWST . mtMap unRWST
instance MonadFunctor (RWST r o s) where
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
  rwsE = mtCounit . rwsCommute
instance (Monad m, Monoid o) => MonadRWS r o s (RWST r o s m) where

deriving instance (MonadZero m, Monoid o) => MonadZero (RWST r o s m)
deriving instance (MonadMaybeI m, Monoid o) => MonadMaybeI (RWST r o s m)
deriving instance (MonadMaybeE m, Monoid o) => MonadMaybeE (RWST r o s m)
deriving instance (MonadMaybe m, Monoid o) => MonadMaybe (RWST r o s m)

-- }}}

-- MaybeT {{{

maybeCommute :: (Functor m) => MaybeT (MaybeT m) ~> MaybeT (MaybeT m)
maybeCommute aMM = MaybeT $ MaybeT $ map ff $ runMaybeT $ runMaybeT aMM
  where
    ff Nothing = Just Nothing
    ff (Just Nothing) = Nothing
    ff (Just (Just a)) = Just (Just a)
  
instance (Unit m) => Unit (MaybeT m) where
  unit = MaybeT . unit . Just
instance (Functor m) => Functor (MaybeT m) where
  map f = MaybeT . map (map f) . runMaybeT
instance (Applicative m) => Applicative (MaybeT m) where
  aM1 <*> aM2 = MaybeT $ map (uncurry ff) $ runMaybeT aM1 <*> runMaybeT aM2
    where
      ff Nothing _ = Nothing
      ff _ Nothing = Nothing
      ff (Just a1) (Just a2) = Just (a1, a2)
instance (Monad m) => Monad (MaybeT m) where
  aM >>= k = MaybeT $ do
    aM' <- runMaybeT aM
    case aM' of
      Nothing -> return Nothing
      Just a -> runMaybeT $ k a
instance MonadUnit MaybeT where
  mtUnit = MaybeT . map Just
instance MonadCounit MaybeT where
  mtCounit = MaybeT . map ff . runMaybeT . runMaybeT
    where
      ff Nothing = Nothing
      ff (Just Nothing) = Nothing
      ff (Just (Just a)) = Just a
instance MonadFunctor MaybeT where
  mtMap :: (m ~> n) -> MaybeT m ~> MaybeT n
  mtMap f = MaybeT . f . runMaybeT

instance (Monad m) => MonadMaybeI (MaybeT m) where
  maybeI :: MaybeT m ~> MaybeT (MaybeT m)
  maybeI = maybeCommute . mtUnit
instance (Monad m) => MonadMaybeE (MaybeT m) where
  maybeE :: MaybeT (MaybeT m) ~> MaybeT m
  maybeE = mtCounit . maybeCommute

-- }}}

-- ListSetT {{{

listSetCommute :: (Functor m) => ListSetT (ListSetT m) ~> ListSetT (ListSetT m)
listSetCommute = ListSetT . ListSetT . map (ListSet . map ListSet . transpose . map runListSet . runListSet) . runListSetT . runListSetT

instance (Unit m) => Unit (ListSetT m) where
  unit = ListSetT . unit . ListSet . singleton
instance (Functor m) => Functor (ListSetT m) where
  map f aM = ListSetT $ map (map f) $ runListSetT aM
instance (Monad m, Functorial JoinLattice m) => Applicative (ListSetT m) where
  (<*>) = mpair
instance (Monad m, Functorial JoinLattice m) => Monad (ListSetT m) where
  (>>=) :: forall a b. ListSetT m a -> (a -> ListSetT m b) -> ListSetT m b
  aM >>= k = ListSetT $ do
    xs <- runListSetT aM
    runListSetT $ msums $ map k xs
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
instance MonadUnit ListSetT where
  mtUnit = ListSetT . map unit
instance MonadCounit ListSetT where
  mtCounit = ListSetT . map concat . runListSetT . runListSetT
instance MonadFunctor ListSetT where
  mtMap f aM = ListSetT $ f $ runListSetT aM

instance (Monad m, Functorial JoinLattice m) => MonadListSetI (ListSetT m) where
  listSetI :: ListSetT m ~> ListSetT (ListSetT m)
  listSetI = listSetCommute . mtUnit
instance (Monad m, Functorial JoinLattice m) => MonadListSetE (ListSetT m) where
  listSetE :: ListSetT (ListSetT m) ~> ListSetT m
  listSetE = mtCounit . listSetCommute
instance (Monad m, Functorial JoinLattice m) => MonadListSet (ListSetT m) where

instance (Monad m, Functorial JoinLattice m) => MonadZero (ListSetT m) where
  mzero :: forall a. ListSetT m a
  mzero = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT bot
instance (Monad m, Functorial JoinLattice m) => MonadPlus (ListSetT m) where
  (<+>) :: forall a. ListSetT m a -> ListSetT m a -> ListSetT m a
  aM1 <+> aM2 = 
    with (functorial :: W (JoinLattice (m (ListSet a)))) $
    ListSetT $ runListSetT aM1 \/ runListSetT aM2
-- PROOF of: associativity, commutativity, zero and unit of <+> for (ListSetT m) {{{
--
-- Follows trivially from definition and Lattice/Zero laws for underlying monad.
--
-- (The lattice of the underlying monads must act as a zero for bind.)
-- QED }}}

-- }}}

----------------------
-- Monads Commuting --
----------------------

-- listSetTStateTCommute :: (Monad m) => ListSetT (StateT s m) a -> StateT s (ListSetT m) a
-- listSetTStateTCommute aSL = StateT $ \ s -> ListSetT $ do
--   (xs, s') <- unStateT (runListSetT aSL) s
--   return $ map (,s') xs
-- stateTListSetTCommute :: (Monad m, JoinLattice s) => StateT s (ListSetT m) a -> ListSetT (StateT s m) a
-- stateTListSetTCommute aLS = ListSetT $ StateT $ \ s -> do
--   xss <- runListSetT $ unStateT aLS s
--   let (xs, ss) = unzip $ runListSet xss
--   return (ListSet xs, joins ss)

-- instance (MonadStateI s m, Functorial JoinLattice m) => MonadStateI s (ListSetT m) where
--   stateI = listSetTStateTCommute . mtMap stateI
-- instance (MonadStateE s m, Functorial JoinLattice m, JoinLattice s) => MonadStateE s (ListSetT m) where
--   stateE = mtMap stateE . stateTListSetTCommute
-- instance (MonadState s m, Functorial JoinLattice m, JoinLattice s) => MonadState s (ListSetT m) where

-- {{{

-- Reader // * {{{

-- Reader // Writer {{{

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

-- Reader // State {{{

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

-- Reader // Maybe {{{

readerMaybeCommute :: (Monad m) => ReaderT r (MaybeT m) ~> MaybeT (ReaderT r m)
readerMaybeCommute aRMM = MaybeT $ ReaderT $ \ r -> runMaybeT $ runReaderT r aRMM

maybeReaderCommute :: (Monad m) => MaybeT (ReaderT r m) ~> ReaderT r (MaybeT m)
maybeReaderCommute aMRM = ReaderT $ \ r -> MaybeT $ runReaderT r $ runMaybeT aMRM

instance (MonadMaybeI m) => MonadMaybeI (ReaderT r m) where
  maybeI :: ReaderT r m ~> MaybeT (ReaderT r m)
  maybeI = readerMaybeCommute . mtMap maybeI
instance (MonadMaybeE m) => MonadMaybeE (ReaderT r m) where
  maybeE :: MaybeT (ReaderT r m) ~> ReaderT r m
  maybeE = mtMap maybeE . maybeReaderCommute
instance (MonadMaybe m) => MonadMaybe (ReaderT r m) where

instance (MonadReaderI r m) => MonadReaderI r (MaybeT m) where
  readerI :: MaybeT m ~> ReaderT r (MaybeT m)
  readerI = maybeReaderCommute . mtMap readerI
instance (MonadReaderE r m) => MonadReaderE r (MaybeT m) where
  readerE :: ReaderT r (MaybeT m) ~> MaybeT m
  readerE = mtMap readerE . readerMaybeCommute
instance (MonadReader r m) => MonadReader r (MaybeT m) where

-- }}}

-- Reader // Error {{{

-- readerErrorCommute :: (Monad m) => ReaderT r (ErrorT e m) ~> ErrorT e (ReaderT r m)
-- readerErrorCommute aRMM = ErrorT $ ReaderT $ \ r -> runErrorT $ runReaderT r aRMM
-- 
-- errorReaderCommute :: (Monad m) => ErrorT e (ReaderT r m) ~> ReaderT r (ErrorT e m)
-- errorReaderCommute aMRM = ReaderT $ \ r -> ErrorT $ runReaderT r $ runErrorT aMRM
-- 
-- instance (MonadErrorI e m) => MonadErrorI e (ReaderT r m) where
--   errorI :: ReaderT r m ~> ErrorT e (ReaderT r m)
--   errorI = readerErrorCommute . mtMap errorI
-- instance (MonadErrorE e m) => MonadErrorE e (ReaderT r m) where
--   errorE :: ErrorT e (ReaderT r m) ~> ReaderT r m
--   errorE = mtMap errorE . errorReaderCommute
-- instance (MonadError e m) => MonadError e (ReaderT r m) where
-- 
-- instance (MonadReaderI r m) => MonadReaderI r (ErrorT e m) where
--   readerI :: ErrorT e m ~> ReaderT r (ErrorT e m)
--   readerI = errorReaderCommute . mtMap readerI
-- instance (MonadReaderE r m) => MonadReaderE r (ErrorT e m) where
--   readerE :: ReaderT r (ErrorT e m) ~> ErrorT e m
--   readerE = mtMap readerE . readerErrorCommute
-- instance (MonadReader r m) => MonadReader r (ErrorT e m) where

-- }}}

-- Reader // MCont {{{

-- readerMContCommute :: (Monad m) => ReaderT r (MContT e m) ~> MContT e (ReaderT r m)
-- readerMContCommute aRMM = MContT $ \ (k :: a -> ReaderT r m e) -> ReaderT $ \ r -> 
--   runMContT (runReaderT r aRMM) $ runReaderT r . k
-- 
-- mContReaderCommute :: (Monad m) => MContT e (ReaderT r m) ~> ReaderT r (MContT e m)
-- mContReaderCommute aMRM = ReaderT $ \ r -> MContT $ \ (k :: a -> m e) ->
--   runReaderT r $ runMContT aMRM $ lift . k
-- 
-- instance (MonadMContI e m) => MonadMContI e (ReaderT r m) where
--   mContI :: ReaderT r m ~> MContT e (ReaderT r m)
--   mContI = readerMContCommute . mtMap mContI
-- instance (MonadMContE e m) => MonadMContE e (ReaderT r m) where
--   mContE :: MContT e (ReaderT r m) ~> ReaderT r m
--   mContE = mtMap mContE . mContReaderCommute
-- instance (MonadMCont e m) => MonadMCont e (ReaderT r m) where
-- 
-- instance (MonadReader r m) => MonadReaderI r (MContT e m) where
--   readerI :: MContT e m ~> ReaderT r (MContT e m)
--   readerI = mContReaderCommute . mtIsoMap (readerI, readerE)
-- instance (MonadReader r m) => MonadReaderE r (MContT e m) where
--   readerE :: ReaderT r (MContT e m) ~> MContT e m
--   readerE = mtIsoMap (readerE, readerI) . readerMContCommute
-- instance (MonadReader r m) => MonadReader r (MContT e m) where

-- }}}

-- Reader // PCont {{{

-- readerPContCommute :: (Monad m) => ReaderT r (PContT m) ~> PContT (ReaderT r m)
-- readerPContCommute aRMM = PContT $ \ (k :: a -> ReaderT r m e) -> ReaderT $ \ r -> 
--   runPContT (runReaderT r aRMM) $ \ a -> runReaderT r $ k a
-- 
-- pContReaderCommute :: (Monad m) => PContT (ReaderT r m) ~> ReaderT r (PContT m)
-- pContReaderCommute aMRM = ReaderT $ \ r -> PContT $ \ (k :: a -> m e) ->
--   runReaderT r $ runPContT aMRM $ \ a -> lift $ k a
-- 
-- instance (MonadPContI m) => MonadPContI (ReaderT r m) where
--   pContI :: ReaderT r m ~> PContT (ReaderT r m)
--   pContI = readerPContCommute . mtMap pContI
-- instance (MonadPContE m) => MonadPContE (ReaderT r m) where
--   pContE :: PContT (ReaderT r m) ~> ReaderT r m
--   pContE = mtMap pContE . pContReaderCommute
-- instance (MonadPCont m) => MonadPCont (ReaderT r m) where
-- 
-- instance (MonadReader r m) => MonadReaderI r (PContT m) where
--   readerI :: PContT m ~> ReaderT r (PContT m)
--   readerI = pContReaderCommute . mtIsoMap (readerI, readerE)
-- instance (MonadReader r m) => MonadReaderE r (PContT m) where
--   readerE :: ReaderT r (PContT m) ~> PContT m
--   readerE = mtIsoMap (readerE, readerI) . readerPContCommute
-- instance (MonadReader r m) => MonadReader r (PContT m) where

-- }}}

-- Reader // RWST {{{

readerRWSCommute :: (Functor m) => ReaderT r1 (RWST r2 o s m) ~> RWST r2 o s (ReaderT r1 m)
readerRWSCommute =
    RWST
  . mtMap 
    ( mtMap readerStateCommute
    . readerWriterCommute
    )
  . readerCommute
  . mtMap unRWST

rwsReaderCommute :: (Functor m) => RWST r1 o s (ReaderT r2 m) ~> ReaderT r2 (RWST r1 o s m)
rwsReaderCommute = 
    mtMap RWST
  . readerCommute
  . mtMap 
    ( writerReaderCommute
    . mtMap stateReaderCommute
    )
  . unRWST
       
-- }}}

-- }}}

-- Writer // * {{{

-- Writer // State {{{

writerStateCommute :: (Functor m) => WriterT w (StateT s m) ~> StateT s (WriterT w m)
writerStateCommute aRMM = StateT $ \ s1 -> WriterT $ map ff $ runStateT s1 $ runWriterT aRMM
  where
    ff ((a, w), s) = ((a, s), w)

stateWriterCommute :: (Functor m) => StateT s (WriterT w m) ~> WriterT w (StateT s m)
stateWriterCommute aMRM = WriterT $ StateT $ map ff . runWriterT . unStateT aMRM
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

-- Writer // Maybe {{{

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

instance (Monoid w, MonadMaybeI m) => MonadMaybeI (WriterT w m) where
  maybeI :: WriterT w m ~> MaybeT (WriterT w m)
  maybeI = writerMaybeCommute . mtMap maybeI
instance (Monoid w, MonadMaybeE m) => MonadMaybeE (WriterT w m) where
  maybeE :: MaybeT (WriterT w m) ~> WriterT w m
  maybeE = mtMap maybeE . maybeWriterCommute
instance (Monoid w, MonadMaybe m) => MonadMaybe (WriterT w m) where

instance (Monoid w, MonadWriter w m) => MonadWriterI w (MaybeT m) where
  writerI :: MaybeT m ~> WriterT w (MaybeT m)
  writerI = maybeWriterCommute . mtMap writerI
instance (Monoid w, MonadWriter w m) => MonadWriterE w (MaybeT m) where
  writerE :: WriterT w (MaybeT m) ~> MaybeT m
  writerE = mtMap writerE . writerMaybeCommute
instance (Monoid w, MonadWriter w m) => MonadWriter w (MaybeT m) where

-- }}}

-- Writer // Error {{{

-- writerErrorCommute :: (Monoid w, Monad m) => WriterT w (ErrorT e m) ~> ErrorT e (WriterT w m)
-- writerErrorCommute aRMM = ErrorT $ WriterT $ do
--   eawM <- runErrorT $ runWriterT aRMM
--   return $ case eawM of
--     Left e -> (Left e, null)
--     Right (a, w) -> (Right a, w)
-- 
-- errorWriterCommute :: (Monad m) => ErrorT e (WriterT w m) ~> WriterT w (ErrorT e m)
-- errorWriterCommute aMRM = WriterT $ ErrorT $ do
--   (eaM, w) <- runWriterT $ runErrorT aMRM
--   return $ case eaM of
--     Left e -> Left e
--     Right a -> Right (a, w)
-- 
-- instance (Monoid w, MonadErrorI e m) => MonadErrorI e (WriterT w m) where
--   errorI :: WriterT w m ~> ErrorT e (WriterT w m)
--   errorI = writerErrorCommute . mtMap errorI
-- instance (Monoid w, MonadErrorE e m) => MonadErrorE e (WriterT w m) where
--   errorE :: ErrorT e (WriterT w m) ~> WriterT w m
--   errorE = mtMap errorE . errorWriterCommute
-- instance (Monoid w, MonadError e m) => MonadError e (WriterT w m) where
-- 
-- instance (Monoid w, MonadWriter w m) => MonadWriterI w (ErrorT e m) where
--   writerI :: ErrorT e m ~> WriterT w (ErrorT e m)
--   writerI = errorWriterCommute . mtMap writerI
-- instance (Monoid w, MonadWriter w m) => MonadWriterE w (ErrorT e m) where
--   writerE :: WriterT w (ErrorT e m) ~> ErrorT e m
--   writerE = mtMap writerE . writerErrorCommute
-- instance (Monoid w, MonadWriter w m) => MonadWriter w (ErrorT e m) where

-- }}}

-- Writer // MCont {{{

-- writerMContCommute :: (Monoid w, Monad m) => WriterT w (MContT e m) ~> MContT e (WriterT w m)
-- writerMContCommute aRMM = MContT $ \ (k :: a -> WriterT w m e) -> WriterT $
--   mmap (,null) $ runMContT (runWriterT aRMM) $ mmap fst . runWriterT . k . fst
-- 
-- mContWriterCommute :: (Monoid w, Monad m) => MContT e (WriterT w m) ~> WriterT w (MContT e m)
-- mContWriterCommute aMRM = WriterT $ MContT $ \ (k :: (a, w) -> m e) -> do
--   mmap fst $ runWriterT $ runMContT aMRM $ lift . k . (,null)
-- 
-- instance (Monoid w, MonadMContI e m) => MonadMContI e (WriterT w m) where
--   mContI :: WriterT w m ~> MContT e (WriterT w m)
--   mContI = writerMContCommute . mtMap mContI
-- instance (Monoid w, MonadMContE e m) => MonadMContE e (WriterT w m) where
--   mContE :: MContT e (WriterT w m) ~> WriterT w m
--   mContE = mtMap mContE . mContWriterCommute
-- instance (Monoid w, MonadMCont e m) => MonadMCont e (WriterT w m) where
-- 
-- instance (Monoid w, MonadWriter w m) => MonadWriterI w (MContT e m) where
--   writerI :: MContT e m ~> WriterT w (MContT e m)
--   writerI = mContWriterCommute . mtIsoMap (writerI, writerE)
-- instance (Monoid w, MonadWriter w m) => MonadWriterE w (MContT e m) where
--   writerE :: WriterT w (MContT e m) ~> MContT e m
--   writerE = mtIsoMap (writerE, writerI) . writerMContCommute
-- instance (Monoid w, MonadWriter w m) => MonadWriter w (MContT e m) where

-- }}}

-- Writer // PCont {{{

-- writerPContCommute :: (Monoid w, Monad m) => WriterT w (PContT m) ~> PContT (WriterT w m)
-- writerPContCommute aRMM = PContT $ \ (k :: a -> WriterT w m e) -> WriterT $
--   runPContT (runWriterT aRMM) $ runWriterT . extend k . WriterT . return
-- 
-- pContWriterCommute :: (Monoid w, Monad m) => PContT (WriterT w m) ~> WriterT w (PContT m)
-- pContWriterCommute aMRM = WriterT $ PContT $ \ (k :: (a, w) -> m e) ->
--   mmap fst $ runWriterT $ runPContT aMRM $ WriterT . mmap (,null) . k . (,null)
-- 
-- instance (Monoid w, MonadPContI m) => MonadPContI (WriterT w m) where
--   pContI :: WriterT w m ~> PContT (WriterT w m)
--   pContI = writerPContCommute . mtMap pContI
-- instance (Monoid w, MonadPContE m) => MonadPContE (WriterT w m) where
--   pContE :: PContT (WriterT w m) ~> WriterT w m
--   pContE = mtMap pContE . pContWriterCommute
-- instance (Monoid w, MonadPCont m) => MonadPCont (WriterT w m) where
-- 
-- instance (Monoid w, MonadWriter w m) => MonadWriterI w (PContT m) where
--   writerI :: PContT m ~> WriterT w (PContT m)
--   writerI = pContWriterCommute . mtIsoMap (writerI, writerE)
-- instance (Monoid w, MonadWriter w m) => MonadWriterE w (PContT m) where
--   writerE :: WriterT w (PContT m) ~> PContT m
--   writerE = mtIsoMap (writerE, writerI) . writerPContCommute
-- instance (Monoid w, MonadWriter w m) => MonadWriter w (PContT m) where

-- }}}

-- Writer // RWST {{{

writerRWSCommute :: (Monad m, Monoid o2) => WriterT o1 (RWST r o2 s m) ~> RWST r o2 s (WriterT o1 m)
writerRWSCommute =
    RWST
  . mtMap 
    ( mtMap writerStateCommute
    . writerCommute
    )
  . writerReaderCommute
  . mtMap unRWST

rwsWriterCommute :: (Functor m, Monoid o1) => RWST r o1 s (WriterT o2 m) ~> WriterT o2 (RWST r o1 s m)
rwsWriterCommute =
    mtMap RWST
  . readerWriterCommute
  . mtMap 
    ( writerCommute
    . mtMap stateWriterCommute
    )
  . unRWST

-- }}}

-- }}}

-- State // * {{{

-- State // Maybe {{{

stateMaybeCommute :: (Monad m) => StateT s (MaybeT m) ~> MaybeT (StateT s m)
stateMaybeCommute aSMM = MaybeT $ StateT $ \ s1 -> do
  asM <- runMaybeT $ runStateT s1 aSMM
  return $ case asM of
    Nothing -> (Nothing, s1)
    Just (a, s2) -> (Just a, s2)

maybeStateCommute :: (Monad m) => MaybeT (StateT s m) ~> StateT s (MaybeT m)
maybeStateCommute aMSM = StateT $ \ s1 -> MaybeT $ do
  (aM, s2) <- runStateT s1 $ runMaybeT aMSM
  return $ case aM of
    Nothing -> Nothing
    Just a -> Just (a, s2)

instance (MonadMaybeI m) => MonadMaybeI (StateT s m) where
  maybeI :: StateT s m ~> MaybeT (StateT s m)
  maybeI aSM = stateMaybeCommute $ mtMap maybeI aSM
instance (MonadMaybeE m) => MonadMaybeE (StateT s m) where
  maybeE :: MaybeT (StateT s m) ~> StateT s m
  maybeE aMSM = mtMap maybeE $ maybeStateCommute aMSM
instance (MonadMaybe m) => MonadMaybe (StateT s m) where

instance (MonadStateI s m) => MonadStateI s (MaybeT m) where
  stateI :: MaybeT m ~> StateT s (MaybeT m)
  stateI aMM = maybeStateCommute $ mtMap stateI aMM
instance (MonadStateE s m) => MonadStateE s (MaybeT m) where
  stateE :: StateT s (MaybeT m) ~> MaybeT m
  stateE aSMM = mtMap stateE $ stateMaybeCommute aSMM
instance (MonadState s m) => MonadState s (MaybeT m) where

-- }}}

-- State // Error {{{

-- stateErrorCommute :: (Monad m) => StateT s (ErrorT e m) ~> ErrorT e (StateT s m)
-- stateErrorCommute aRMM = ErrorT $ StateT $ \ s1 -> do
--   easM <- runErrorT $ runStateT s1 aRMM
--   return $ case easM of
--     Left e -> (Left e, s1)
--     Right (a, s2) -> (Right a, s2)
-- 
-- errorStateCommute :: (Monad m) => ErrorT e (StateT s m) ~> StateT s (ErrorT e m)
-- errorStateCommute aMRM = StateT $ \ s1 -> ErrorT $ do
--   (eaM, s2) <- runStateT s1 $ runErrorT aMRM
--   return $ case eaM of
--     Left e -> Left e
--     Right a -> Right (a, s2)
-- 
-- instance (MonadErrorI e m) => MonadErrorI e (StateT s m) where
--   errorI :: StateT s m ~> ErrorT e (StateT s m)
--   errorI = stateErrorCommute . mtMap errorI
-- instance (MonadErrorE e m) => MonadErrorE e (StateT s m) where
--   errorE :: ErrorT e (StateT s m) ~> StateT s m
--   errorE = mtMap errorE . errorStateCommute
-- instance (MonadError e m) => MonadError e (StateT s m) where
-- 
-- instance (MonadStateI s m) => MonadStateI s (ErrorT e m) where
--   stateI :: ErrorT e m ~> StateT s (ErrorT e m)
--   stateI = errorStateCommute . mtMap stateI
-- instance (MonadStateE s m) => MonadStateE s (ErrorT e m) where
--   stateE :: StateT s (ErrorT e m) ~> ErrorT e m
--   stateE = mtMap stateE . stateErrorCommute
-- instance (MonadState s m) => MonadState s (ErrorT e m) where

-- }}}

-- State // MCont {{{

-- stateMContCommute :: (Monad m) => StateT s (MContT e m) ~> MContT e (StateT s m)
-- stateMContCommute aRMM = MContT $ \ (k :: a -> StateT s m e) -> StateT $ \ s -> 
--   mmap (,s) $ runMContT (runStateT s aRMM) $ mmap fst . runStateT s . k . fst
-- 
-- mContStateCommute :: (Monad m) => MContT e (StateT s m) ~> StateT s (MContT e m)
-- mContStateCommute aMRM = StateT $ \ s -> MContT $ \ (k :: (a, s) -> m e) ->
--   mmap fst $ runStateT s $ runMContT aMRM $ \ a -> lift $ k (a, s)
-- 
-- instance (MonadMContI e m) => MonadMContI e (StateT s m) where
--   mContI :: StateT s m ~> MContT e (StateT s m)
--   mContI = stateMContCommute . mtMap mContI
-- instance (MonadMContE e m) => MonadMContE e (StateT s m) where
--   mContE :: MContT e (StateT s m) ~> StateT s m
--   mContE = mtMap mContE . mContStateCommute
-- instance (MonadMCont e m) => MonadMCont e (StateT s m) where
-- 
-- instance (MonadState s m) => MonadStateI s (MContT e m) where
--   stateI :: MContT e m ~> StateT s (MContT e m)
--   stateI = mContStateCommute . mtIsoMap (stateI, stateE)
-- instance (MonadState s m) => MonadStateE s (MContT e m) where
--   stateE :: StateT s (MContT e m) ~> MContT e m
--   stateE = mtIsoMap (stateE, stateI) . stateMContCommute
-- instance (MonadState s m) => MonadState s (MContT e m) where

-- }}}

-- State // PCont {{{

-- statePContCommute :: (Monad m) => StateT s (PContT m) ~> PContT (StateT s m)
-- statePContCommute aSMM = PContT $ \ (k :: a -> StateT s m e) -> StateT $ \ s1 -> 
--   runPContT (runStateT s1 aSMM) $ \ (a, s2) -> runStateT s2 $ k a
-- 
-- pContStateCommute :: (Monad m) => PContT (StateT s m) ~> StateT s (PContT m)
-- pContStateCommute aMSM = StateT $ \ s -> PContT $ \ (k :: (a, s) -> m e) ->
--   mmap fst $ runStateT s $ runPContT aMSM $ lift . k . (,s)
-- 
-- instance (MonadPContI m) => MonadPContI (StateT s m) where
--   pContI :: StateT s m ~> PContT (StateT s m)
--   pContI = statePContCommute . mtMap pContI
-- instance (MonadPContE m) => MonadPContE (StateT s m) where
--   pContE :: PContT (StateT s m) ~> StateT s m
--   pContE = mtMap pContE . pContStateCommute
-- instance (MonadPCont m) => MonadPCont (StateT s m) where
-- 
-- instance (MonadState s m) => MonadStateI s (PContT m) where
--   stateI :: PContT m ~> StateT s (PContT m)
--   stateI = pContStateCommute . mtIsoMap (stateI, stateE)
-- instance (MonadState s m) => MonadStateE s (PContT m) where
--   stateE :: StateT s (PContT m) ~> PContT m
--   stateE = mtIsoMap (stateE, stateI) . statePContCommute
-- instance (MonadState s m) => MonadState s (PContT m) where

-- }}}

-- State // RWST {{{

stateRWSCommute :: (Monad m, Monoid o) => StateT s1 (RWST r o s2 m) ~> RWST r o s2 (StateT s1 m)
stateRWSCommute =
    RWST
  . mtMap 
    ( mtMap stateCommute
    . stateWriterCommute
    )
  . stateReaderCommute
  . mtMap unRWST

rwsStateCommute :: (Functor m, Monoid o) => RWST r o s1 (StateT s2 m) ~> StateT s2 (RWST r o s1 m)
rwsStateCommute =
    mtMap RWST
  . readerStateCommute
  . mtMap 
    ( writerStateCommute
    . mtMap stateCommute
    )
  . unRWST

-- }}}

-- State // ListSet {{{

stateListSetCommute :: (Functor m, JoinLattice s) => StateT s (ListSetT m) ~> ListSetT (StateT s m)
stateListSetCommute aMM = ListSetT $ StateT $ \ s -> map ff $ runListSetT $ runStateT s aMM
  where
    ff asL = (map fst asL, joins $ map snd asL)

listSetStateCommute :: (Functor m) => ListSetT (StateT s m) ~> StateT s (ListSetT m)
listSetStateCommute aMM = StateT $ \ s -> ListSetT $ map ff $ runStateT s $ runListSetT aMM
  where
    ff (xs, s) = map (,s) xs

instance (MonadListSetI m, JoinLattice s) => MonadListSetI (StateT s m) where
  listSetI :: StateT s m ~> ListSetT (StateT s m)
  listSetI = stateListSetCommute . mtMap listSetI
instance (MonadListSetE m) => MonadListSetE (StateT s m) where
  listSetE :: ListSetT (StateT s m) ~> StateT s m
  listSetE = mtMap listSetE . listSetStateCommute
instance (MonadListSet m, JoinLattice s) => MonadListSet (StateT s m) where

instance (MonadStateI s m, Functorial JoinLattice m) => MonadStateI s (ListSetT m) where
  stateI :: ListSetT m ~> StateT s (ListSetT m)
  stateI = listSetStateCommute . mtMap stateI
instance (MonadStateE s m, Functorial JoinLattice m, JoinLattice s) => MonadStateE s (ListSetT m) where
  stateE :: StateT s (ListSetT m) ~> ListSetT m
  stateE = mtMap stateE . stateListSetCommute
instance (MonadState s m, Functorial JoinLattice m, JoinLattice s) => MonadState s (ListSetT m) where

-- }}}

-- }}}

-- Maybe // * {{{

-- Maybe // Error {{{

-- maybeErrorCommute :: (Monad m) => MaybeT (ErrorT e m) ~> ErrorT e (MaybeT m)
-- maybeErrorCommute aRMM = ErrorT $ MaybeT $ do
--   eaM <- runErrorT $ runMaybeT aRMM
--   return $ case eaM of
--     Left e -> Just $ Left e
--     Right Nothing -> Nothing
--     Right (Just a) -> Just $ Right a
-- 
-- errorMaybeCommute :: (Monad m) => ErrorT e (MaybeT m) ~> MaybeT (ErrorT e m)
-- errorMaybeCommute aMRM = MaybeT $ ErrorT $ do
--   eaM <- runMaybeT $ runErrorT aMRM
--   return $ case eaM of
--     Nothing -> Right Nothing
--     Just (Left e) -> Left e
--     Just (Right a) -> Right $ Just a
-- 
-- instance (MonadErrorI e m) => MonadErrorI e (MaybeT m) where
--   errorI :: MaybeT m ~> ErrorT e (MaybeT m)
--   errorI = maybeErrorCommute . mtMap errorI
-- instance (MonadErrorE e m) => MonadErrorE e (MaybeT m) where
--   errorE :: ErrorT e (MaybeT m) ~> MaybeT m
--   errorE = mtMap errorE . errorMaybeCommute
-- instance (MonadError e m) => MonadError e (MaybeT m) where
-- 
-- instance (MonadMaybe m) => MonadMaybeI (ErrorT e m) where
--   maybeI :: ErrorT e m ~> MaybeT (ErrorT e m)
--   maybeI = errorMaybeCommute . mtMap maybeI
-- instance (MonadMaybe m) => MonadMaybeE (ErrorT e m) where
--   maybeE :: MaybeT (ErrorT e m) ~> ErrorT e m
--   maybeE = mtMap maybeE . maybeErrorCommute
-- instance (MonadMaybe m) => MonadMaybe (ErrorT e m) where

-- }}}

-- Maybe // MCont {{{

-- -- maybeMContCommute :: (Monad m) => MaybeT (MContT e m) ~> MContT e (MaybeT m)
-- -- maybeMContCommute aRMM = MContT $ \ (k :: a -> MaybeT m e) -> MaybeT $
-- --   runMContT (runMaybeT aRMM) $ \ aM -> 
-- --     case aM of
-- --       Nothing -> _
-- --       Just a -> _ $ runMaybeT $ k a
-- 
-- mContMaybeCommute :: (Monad m) => MContT e (MaybeT m) ~> MaybeT (MContT e m)
-- mContMaybeCommute aMRM = MaybeT $ MContT $ \ (k :: Maybe a -> m e) -> do
--   aM <- runMaybeT $ runMContT aMRM $ \ a -> lift $ k $ Just a
--   case aM of
--     Nothing -> k Nothing
--     Just a -> return a
-- 
-- -- instance (MonadMContI e m) => MonadMContI e (MaybeT m) where
-- --   mContI :: MaybeT m ~> MContT e (MaybeT m)
-- --   mContI = maybeMContCommute . mtMap mContI
-- instance (MonadMContE e m) => MonadMContE e (MaybeT m) where
--   mContE :: MContT e (MaybeT m) ~> MaybeT m
--   mContE = mtMap mContE . mContMaybeCommute
-- -- instance (MonadMCont e m) => MonadMCont e (MaybeT m) where
-- 
-- instance (MonadMaybe m) => MonadMaybeI (MContT e m) where
--   maybeI :: MContT e m ~> MaybeT (MContT e m)
--   maybeI = mContMaybeCommute . mtIsoMap (maybeI, maybeE)
-- -- instance (MonadMaybe m) => MonadMaybeE (MContT e m) where
-- --   maybeE :: MaybeT (MContT e m) ~> MContT e m
-- --   maybeE = mtIsoMap (maybeE, maybeI) . maybeMContCommute
-- -- instance (MonadMaybe m) => MonadMaybe (MContT e m) where

-- }}}

-- Maybe // PCont {{{

-- maybePContCommute :: (Monad m) => MaybeT (PContT m) ~> PContT (MaybeT m)
-- maybePContCommute aSMM = PContT $ \ (k :: a -> MaybeT m e) -> MaybeT $
--   runPContT (runMaybeT aSMM) $ \ aM -> runMaybeT $ MaybeT (return aM) >>= k
-- 
-- pContMaybeCommute :: (Monad m) => PContT (MaybeT m) ~> MaybeT (PContT m)
-- pContMaybeCommute aMSM = MaybeT $ PContT $ \ (k :: Maybe a -> m b) -> do
--   aM <- runMaybeT $ runPContT aMSM $ \ a -> lift $ k $ Just a
--   case aM of
--     Nothing -> k Nothing
--     Just a -> return a
-- 
-- instance (MonadPContI m) => MonadPContI (MaybeT m) where
--   pContI :: MaybeT m ~> PContT (MaybeT m)
--   pContI = maybePContCommute . mtMap pContI
-- instance (MonadPContE m) => MonadPContE (MaybeT m) where
--   pContE :: PContT (MaybeT m) ~> MaybeT m
--   pContE = mtMap pContE . pContMaybeCommute
-- instance (MonadPCont m) => MonadPCont (MaybeT m) where
-- 
-- instance (MonadMaybe m) => MonadMaybeI (PContT m) where
--   maybeI :: PContT m ~> MaybeT (PContT m)
--   maybeI = pContMaybeCommute . mtIsoMap (maybeI, maybeE)
-- instance (MonadMaybe m) => MonadMaybeE (PContT m) where
--   maybeE :: MaybeT (PContT m) ~> PContT m
--   maybeE = mtIsoMap (maybeE, maybeI) . maybePContCommute
-- instance (MonadMaybe m) => MonadMaybe (PContT m) where

-- }}}

-- }}}

-- Error // * {{{

-- Error // MCont {{{

-- -- errorMContCommute :: (Monad m) => ErrorT e (MContT r m) ~> MContT r (ErrorT e m)
-- -- errorMContCommute aSMM = MContT $ \ (k :: a -> ErrorT e m r) -> ErrorT $
-- --   runMContT (runErrorT aSMM) $ \ aM -> 
-- --     case aM of
-- --       Left e -> _
-- --       Right a -> _ $ runErrorT $ k a
-- 
-- mContErrorCommute :: (Monad m) => MContT r (ErrorT e m) ~> ErrorT e (MContT r m)
-- mContErrorCommute aMSM = ErrorT $ MContT $ \ (k :: e :+: a -> m b) -> do
--   aM <- runErrorT $ runMContT aMSM $ \ a -> lift $ k $ Right a
--   case aM of
--     Left e -> k $ Left e
--     Right a -> return a
-- 
-- -- instance (MonadMContI r m) => MonadMContI r (ErrorT e m) where
-- --   mContI :: ErrorT e m ~> MContT r (ErrorT e m)
-- --   mContI = errorMContCommute . mtMap mContI
-- instance (MonadMContE r m) => MonadMContE r (ErrorT e m) where
--   mContE :: MContT r (ErrorT e m) ~> ErrorT e m
--   mContE = mtMap mContE . mContErrorCommute
-- -- instance (MonadMCont r m) => MonadMCont r (ErrorT e m) where
-- 
-- instance (MonadError e m) => MonadErrorI e (MContT r m) where
--   errorI :: MContT r m ~> ErrorT e (MContT r m)
--   errorI = mContErrorCommute . mtIsoMap (errorI, errorE)
-- -- instance (MonadError e m) => MonadErrorE e (MContT r m) where
-- --   errorE :: ErrorT e (MContT r m) ~> MContT r m
-- --   errorE = mtIsoMap (errorE, errorI) . errorMContCommute
-- -- instance (MonadError e m) => MonadError e (MContT r m) where

-- }}}

-- Error // PCont {{{

-- errorPContCommute :: (Monad m) => ErrorT e (PContT m) ~> PContT (ErrorT e m)
-- errorPContCommute aSMM = PContT $ \ (k :: a -> ErrorT e m b) -> ErrorT $
--   runPContT (runErrorT aSMM) $ \ aM -> runErrorT $ ErrorT (return aM) >>= k
-- 
-- pContErrorCommute :: (Monad m) => PContT (ErrorT e m) ~> ErrorT e (PContT m)
-- pContErrorCommute aMSM = ErrorT $ PContT $ \ (k :: e :+: a -> m b) -> do
--   aM <- runErrorT $ runPContT aMSM $ \ a -> lift $ k $ Right a
--   case aM of
--     Left e -> k $ Left e
--     Right a -> return a
-- 
-- instance (MonadPContI m) => MonadPContI (ErrorT e m) where
--   pContI :: ErrorT e m ~> PContT (ErrorT e m)
--   pContI = errorPContCommute . mtMap pContI
-- instance (MonadPContE m) => MonadPContE (ErrorT e m) where
--   pContE :: PContT (ErrorT e m) ~> ErrorT e m
--   pContE = mtMap pContE . pContErrorCommute
-- instance (MonadPCont m) => MonadPCont (ErrorT e m) where
-- 
-- instance (MonadError e m) => MonadErrorI e (PContT m) where
--   errorI :: PContT m ~> ErrorT e (PContT m)
--   errorI = pContErrorCommute . mtIsoMap (errorI, errorE)
-- instance (MonadError e m) => MonadErrorE e (PContT m) where
--   errorE :: ErrorT e (PContT m) ~> PContT m
--   errorE = mtIsoMap (errorE, errorI) . errorPContCommute
-- instance (MonadError e m) => MonadError e (PContT m) where

-- }}}

-- Error // List {{{

-- errorListCommute :: (Monad m) => ErrorT e (ListT m) a -> ListT (ErrorT e m) a
-- errorListCommute aELM = ListT $ ErrorT $ do
--   aM <- unconsListT $ runErrorT aELM
--   case aM of
--     Nothing -> return $ Right Nothing
--     Just (ea, eaLM) -> case ea of
--       Left e -> return $ Left e
--       Right a -> return $ Right $ Just (a, errorListCommute $ ErrorT eaLM)
-- 
-- listErrorCommute :: (Monad m) => ListT (ErrorT e m) a -> ErrorT e (ListT m) a
-- listErrorCommute aLEM = ErrorT $ ListT $ do
--   aM <- runErrorT $ unconsListT aLEM
--   case aM of
--     Left e -> return $ Just (Left e, mnull)
--     Right Nothing -> return Nothing
--     Right (Just (a, aLEM')) -> return $ Just (Right a, runErrorT $ listErrorCommute aLEM')
-- 
-- instance (MonadListI m) => MonadListI (ErrorT e m) where
--   listI :: ErrorT e m ~> ListT (ErrorT e m)
--   listI = errorListCommute . mtMap listI
-- instance (MonadListE m) => MonadListE (ErrorT e m) where
--   listE :: ListT (ErrorT e m) ~> ErrorT e m
--   listE = mtMap listE . listErrorCommute
-- instance (MonadList m) => MonadList (ErrorT e m) where
--
-- instance (MonadErrorI e m) => MonadErrorI e (ListT m) where
--   errorI :: ListT m ~> ErrorT e (ListT m)
--   errorI = listErrorCommute . mtMap errorI
-- instance (MonadErrorE e m) => MonadErrorE e (ListT m) where
--   errorE :: ErrorT e (ListT m) ~> ListT m
--   errorE = mtMap errorE . errorListCommute
-- instance (MonadError e m) => MonadError e (ListT m) where
-- 

-- }}}

-- }}}

-- MCont // * {{{

-- MCont // PCont {{{

-- mContPContCommute :: forall m r. (Monad m) => MContT r (PContT m) ~> PContT (MContT r m)
-- mContPContCommute aRAM = PContT $ \ (k1 :: a -> MContT r m b) -> MContT $ \ (k2 :: b -> m r) ->
--   execPContT $ runMContT aRAM $ \ a -> lift $ runMContT (k1 a) $ \ b -> k2 b
-- 
-- pContMContCommute :: (Monad m) => PContT (MContT r m) ~> MContT r (PContT m)
-- pContMContCommute aARM = MContT $ \ (k1 :: a -> PContT m r) -> PContT $ \ (k2 :: r -> m b) ->
--   extend k2 $ execMContT $ runPContT aARM $ \ a -> lift $ execPContT $ k1 a
-- 
-- instance (MonadPCont m) => MonadPContI (MContT r m) where
--   pContI :: MContT r m ~> PContT (MContT r m)
--   pContI = mContPContCommute . mtIsoMap (pContI, pContE)
-- instance (MonadPCont m) => MonadPContE (MContT r m) where
--   pContE :: PContT (MContT r m) ~> MContT r m
--   pContE = mtIsoMap (pContE, pContI) . pContMContCommute
-- instance (MonadPCont m) => MonadPCont (MContT r m) where
-- 
-- instance (MonadMCont r m) => MonadMContI r (PContT m) where
--   mContI :: PContT m ~> MContT r (PContT m)
--   mContI = pContMContCommute . mtIsoMap (mContI, mContE)
-- instance (MonadMCont r m) => MonadMContE r (PContT m) where
--   mContE :: MContT r (PContT m) ~> PContT m
--   mContE = mtIsoMap (mContE, mContI) . mContPContCommute
-- instance (MonadMCont r m) => MonadMCont r (PContT m) where

-- }}}

-- }}}

-- PCont // * {{{
-- }}}

-- List // * {{{
-- }}}

-- RWST // * {{{
-- }}}

-- }}} --

