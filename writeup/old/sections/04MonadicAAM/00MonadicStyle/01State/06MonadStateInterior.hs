instance (MonadState s m) => MonadState s (StateT s' m) where
  get = StateT $ \ s -> do
    s' <- get
    return (s',s)
  put s' = StateT $ \ s -> do
    put s'
    return ((),s)

