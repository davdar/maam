newtype StateT_SS s m a = StateT_SS { runStateT_SS :: SS m (a, Cell s) }
instance (Pointed (SS m), JoinLattice (Cell s)) => Pointed (StateT_SS s m) where
  point a = point (a, bot)
instance (MonadStep m) => MonadStep (StateT s m) where
  SS (StateT s m) = StateT_SS s m
  step f xSS = step (\ (a, s) -> runStateT (f a) s) $ runStateT_SS xSS
