newtype StateT s m a = StateT { runStateT ::  Cell s -> m (a,Cell s) }
