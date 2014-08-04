class MonadPlus m where
  mzero :: m a
  mplus :: m a -> m a -> m a
