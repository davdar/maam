class (Pointed (SS m)) => MonadStep m where
  type SS m :: * -> *
  step :: (a -> m b) -> SS m a -> SS m b
