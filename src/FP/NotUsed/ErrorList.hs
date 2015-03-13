-- ErrorList {{{

data ErrorList e a =
    ErrorListFailure [e]
  | ErrorListSuccess a [a]

instance Monoid (ErrorList e a) where
  null = ErrorListFailure []
  ErrorListFailure e1 ++ ErrorListFailure e2 = ErrorListFailure $ e1 ++ e2
  ErrorListSuccess x xs ++ ErrorListSuccess y ys = ErrorListSuccess x (xs ++ (y:ys))
  ErrorListFailure _ ++ ys = ys
  xs ++ ErrorListFailure _ = xs
instance Functorial Monoid (ErrorList e) where functorial = W
instance Unit (ErrorList e) where
  unit x = ErrorListSuccess x []
instance Functor (ErrorList e) where
  map = mmap
instance Product (ErrorList e) where
  (<*>) = mpair
instance Applicative (ErrorList e) where
  (<@>) = mapply
instance Bind (ErrorList e) where
  ErrorListFailure e >>= _ = ErrorListFailure e
  ErrorListSuccess x [] >>= k = k x
  ErrorListSuccess x (x':xs') >>= k = k x ++ (ErrorListSuccess x' xs' >>= k)
instance Monad (ErrorList e) where
instance MonadBot (ErrorList e) where
  mbot = null
instance MonadMonoid (ErrorList e) where
  (<++>) = (++)
-- instance CoIterable a (ErrorList e a) where
--   coiter _ i (ErrorListFailure _) = i
--   coiter f i (ErrorListSuccess x xs) = f x $ coiter f i xs
-- instance Buildable a (ErrorList e a) where
--   nil = ErrorListFailure []
--   cons x xs = ErrorListSuccess x $ toList xs

errorListConcat :: ErrorList e (ErrorList e a) -> ErrorList e a
errorListConcat (ErrorListFailure e) = ErrorListFailure e
errorListConcat (ErrorListSuccess x xs) = x ++ concat xs

errorListPluck :: ErrorList e a -> ErrorList e (ErrorList e a) -> [e] :+: (ErrorList e a, ErrorList e (ErrorList e a))
errorListPluck (ErrorListFailure e1) (ErrorListFailure e2) = Inl $ e1 ++ e2
errorListPluck (ErrorListFailure e1) (ErrorListSuccess _ _) = Inl e1
errorListPluck (ErrorListSuccess x xs) (ErrorListFailure _) = Inr (unit x, unit $ fromList xs)
errorListPluck (ErrorListSuccess x1 xs1) (ErrorListSuccess xs2 xss) = do
  (ys2, xss') <- errorListPluck xs2 $ fromList xss
  return (ErrorListSuccess x1 $ toList ys2, ErrorListSuccess (fromList xs1) $ toList xss')

errorListTranspose :: ErrorList e (ErrorList e a) -> ErrorList e (ErrorList e a)
errorListTranspose (ErrorListFailure e) = unit $ ErrorListFailure e
errorListTranspose (ErrorListSuccess xs xss) =
  case errorListPluck xs $ fromList xss of
    Inl e -> ErrorListFailure e
    Inr (ys, xss') -> ErrorListSuccess ys $ toList $ errorListTranspose xss'

-- }}}


-- MonadErrorList {{{

newtype ErrorListT e m a = ErrorListT { unErrorListT :: m (ErrorList e a) }

class (Monad m) => MonadErrorListI e m where
  errorListI :: m ~> ErrorListT e m
class (Monad m) => MonadErrorListE e m where
  errorListE :: ErrorListT e m ~> m
class (MonadErrorListI e m, MonadErrorListE e m) => MonadErrorList e m where

throwErrorList :: (MonadErrorListE e m) => e -> m a
throwErrorList = errorListE . ErrorListT . unit . ErrorListFailure . unit

-- }}}









-- ErrorListT {{{

errorListCommute :: (Functor m) => ErrorListT e (ErrorListT e m) ~> ErrorListT e (ErrorListT e m)
errorListCommute aMM = ErrorListT $ ErrorListT $ errorListTranspose ^$ unErrorListT $ unErrorListT aMM

instance (Unit m) => Unit (ErrorListT e m) where
  unit = ErrorListT . unit . unit
instance (Functor m) => Functor (ErrorListT e m) where
  map f = ErrorListT . f ^^. unErrorListT
instance (Monad m, Functorial Monoid m) => Product (ErrorListT e m) where
  (<*>) = mpair
instance (Monad m, Functorial Monoid m) => Applicative (ErrorListT e m) where
  (<@>) = mapply
instance (Bind m, Functorial Monoid m) => Bind (ErrorListT e m) where
  (>>=) :: forall a b. ErrorListT e m a -> (a -> ErrorListT e m b) -> ErrorListT e m b
  aM >>= k = ErrorListT $ do
    xs <- unErrorListT aM
    unErrorListT $ concat $ k ^$ xs
instance (Monad m, Functorial Monoid m) => Monad (ErrorListT e m) where
instance FunctorUnit2 (ErrorListT e) where
  funit2 = ErrorListT .^ unit
instance FunctorJoin2 (ErrorListT e) where
  fjoin2 = ErrorListT . errorListConcat ^. unErrorListT . unErrorListT
instance FunctorFunctor2 (ErrorListT e) where
  ftMap f = ErrorListT . f . unErrorListT

instance (Functorial Monoid m) => Monoid (ErrorListT e m a) where
  null = 
    with (functorial :: W (Monoid (m (ErrorList e a)))) $
    ErrorListT null
  xs ++ ys =
    with (functorial :: W (Monoid (m (ErrorList e a)))) $
    ErrorListT $ unErrorListT xs ++ unErrorListT ys
instance (Functorial Monoid m) => Functorial Monoid (ErrorListT e m) where functorial = W
instance (Functorial Monoid m) => MonadBot (ErrorListT e m) where
  mbot = null
instance (Functorial Monoid m) => MonadAppend (ErrorListT e m) where
  (<++>) = (++)

instance (Monad m, Functorial Monoid m) => MonadErrorListI e (ErrorListT e m) where
  errorListI :: ErrorListT e m ~> ErrorListT e (ErrorListT e m)
  errorListI = errorListCommute . ftUnit
instance (Monad m, Functorial Monoid m) => MonadErrorListE e (ErrorListT e m) where
  errorListE :: ErrorListT e (ErrorListT e m) ~> ErrorListT e m
  errorListE = ftJoin . errorListCommute
instance (Monad m, Functorial Monoid m) => MonadErrorList e (ErrorListT e m) where

errorToErrorList :: (Functor m) => ErrorT e m ~> ErrorListT e m
errorToErrorList aM = ErrorListT $ ff ^$ unErrorT aM
  where
    ff (Inl e) = ErrorListFailure [e]
    ff (Inr a) = ErrorListSuccess a []

-- this might not be right
errorListToError :: (Monad m, Functorial Monoid m) => ErrorListT e (ErrorListT e m) a -> ErrorT e (ErrorListT e m) a
errorListToError aM = ErrorT $ mconcat . ff *$ unErrorListT aM
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
 

-- State // ErrorList {{{

stateErrorListCommute :: (Functor m, Monoid s) => StateT s (ErrorListT e m) ~> ErrorListT e (StateT s m)
stateErrorListCommute aMM = ErrorListT $ StateT $ \ s -> ff ^$ unErrorListT $ unStateT s aMM
  where
    ff asL = (fst ^$ asL, concat $ snd ^$ asL)

errorListStateCommute :: (Functor m) => ErrorListT e (StateT s m) ~> StateT s (ErrorListT e m)
errorListStateCommute aMM = StateT $ \ s -> ErrorListT $ ff ^$ unStateT s $ unErrorListT aMM
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

instance (Pretty e, Pretty a) => Pretty (ErrorList e a) where
  pretty (ErrorListFailure e) = app [con "Failure", pretty e]
  pretty (ErrorListSuccess x xs) = app [con "Success", pretty (x:xs)]

instance (Functorial Pretty m, Pretty e, Pretty a) => Pretty (ErrorListT e m a) where
  pretty (ErrorListT aM) = 
    with (functorial :: W (Pretty (m (ErrorList e a)))) $
    -- app [con "ErrorListT", pretty aM]
    pretty aM
instance (Functorial Pretty m, Pretty e) => Functorial Pretty (ErrorListT e m) where
  functorial = W

