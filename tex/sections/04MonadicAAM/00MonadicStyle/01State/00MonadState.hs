class MonadState s m where
  get :: m s
  put :: s -> m ()
