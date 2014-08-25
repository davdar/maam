-- MonadDKon {{{

newtype DKonT r m a = DKonT { runDKonT :: (a -> m r) -> (r -> m r) -> m r }
class (Monad m) => MonadDKonI r m | m -> r where
  dkonI :: m ~> DKonT r m
class (Monad m) => MonadDKonE r m | m -> r where
  dkonE :: DKonT r m ~> m
class (MonadDKonI r m, MonadDKonE r m) => MonadDKon r m | m -> r where

callCC :: (MonadDKonE r m) => ((a -> m r) -> (r -> m r) -> m r) -> m a
callCC = dkonE . DKonT

useK :: (MonadDKonI r m) => (a -> m r) -> (r -> m r) -> m a -> m r
useK k1 k2 aM = runDKonT (dkonI aM) k1 k2

callCC1 :: (MonadDKon r m) => ((a -> m r) -> m r) -> m a
callCC1 f = callCC $ \ k1 k2 -> useK return k2 (f k1)

useK1 :: (MonadDKon r m) => (a -> m r) -> m a -> m r
useK1 k aM = useK k return aM

shift :: (MonadDKon r m) => m r -> m r
shift rM = callCC $ \ k1 k2 -> useK (k1 *. k2) return rM

reset :: (MonadDKon r m) => m r -> m r
reset rM = callCC $ \ k1 k2 -> useK return (k1 *. k2) rM

-- }}}

-- DKon {{{

type DKon r = DKonT r ID

runDKon :: DKon r a -> (a -> r) -> (r -> r) -> r
runDKon aM k1 k2 = runID $ runDKonT aM (ID . k1) (ID . k2)

evalDKon :: DKon r r -> r
evalDKon aM = runDKon aM id id

dkonCommute :: forall r m. DKonT r (DKonT r m) ~> DKonT r (DKonT r m)
dkonCommute aMM = DKonT $ \ (k1 :: a -> DKonT r m r) (k2 :: r -> DKonT r m r) -> DKonT $ \ (k3 :: r -> m r) (k4 :: r -> m r) ->
  let aM :: DKonT r m r
      aM = runDKonT aMM 
        (\ (a :: a) -> DKonT $ \ (k1' :: r -> m r) (k2' :: r -> m r) -> runDKonT (k1 a) k2' k1') 
        (\ (r :: r) -> DKonT $ \ (k1' :: r -> m r) (k2' :: r -> m r) -> runDKonT (k2 r) k2' k1')
  in runDKonT aM k4 k3

instance (Monad m) => Unit (DKonT r m) where
  unit a = DKonT $ \ (k1 :: a -> m r) (k2 :: r -> m r) -> k1 a
instance (Monad m) => Product (DKonT r m) where
  (<*>) = mpair
instance (Monad m) => Applicative (DKonT r m) where
  (<@>) = mapply
instance (Monad m) => Functor (DKonT r m) where
  map = mmap
instance (Monad m) => Bind (DKonT r m) where
  (>>=) :: DKonT r m a -> (a -> DKonT r m b) -> DKonT r m b
  aM >>= mk = DKonT $ \ (k1 :: b -> m r) (k2 :: r -> m r) ->
    runDKonT aM (\ a -> runDKonT (mk a) k1 k2) k2
instance (Monad m) => Monad (DKonT r m) where

instance MonadUnit (DKonT r) where
  mtUnit :: (Monad m) => m ~> DKonT r m
  mtUnit aM = DKonT $ \ (k1 :: a -> m r) (k2 :: r -> m r) -> k1 *$ aM
instance MonadCounit (DKonT r) where
  mtCounit :: (Monad m) => DKonT r (DKonT r m) ~> DKonT r m
  mtCounit aMM = DKonT $ \ (k1 :: a -> m r) (k2 :: r -> m r) -> 
    runDKonT (runDKonT aMM (mtUnit . k1) return) return k2

instance (Monad m) => MonadDKonI r (DKonT r m) where
  dkonI :: DKonT r m ~> DKonT r (DKonT r m)
  dkonI = dkonCommute . mtUnit
instance (Monad m) => MonadDKonE r (DKonT r m) where
  dkonE :: DKonT r (DKonT r m) ~> DKonT r m
  dkonE = mtCounit . dkonCommute
instance (Monad m) => MonadDKon r (DKonT r m) where

t1 :: String
t1 = evalDKon $ do
  s1 <- callCC1 $ \ k -> do
    s' <- k "B"
    return $ s' ++ "C"
  return $ s1 ++ "F"
--   s2 <- callCC1 $ \ k -> do
--     s' <- k "D"
--     return $ s' ++ "E"
--   return $ s1 ++ "." ++ s2 ++ "." ++ "F"

-- }}}

