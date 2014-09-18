instance (MonadState s m) => MonadState s (NondetT m) where
  get = NondetT $ do
    s <- get
    return [s]
  put s = NondetT $ do
    put s
    return [()]
