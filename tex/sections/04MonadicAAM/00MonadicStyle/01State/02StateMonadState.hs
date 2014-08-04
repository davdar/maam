instance (Monad m) => MonadState s (StateT s m) where
  get = StateT $ \ s -> return (s,s)
  put s = StateT $ \ _ -> return ((),s)
