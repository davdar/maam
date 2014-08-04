newtype StateT s m a = StateT { runStateT ::  s -> m (a,s) }
instance (Monad m) => Monad (StateT m) where
  return x = StateT $ \ s -> return (x, s)
  xM >>= k = StateT $ \ s -> do
    (x,s') <- runStateT xM s
    runStateT (k x) s'
