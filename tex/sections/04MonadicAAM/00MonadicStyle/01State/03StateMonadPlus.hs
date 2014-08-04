instance (MonadPlus m) => MonadPlus (StateT s m) where
  mzero = StateT $ \ _ -> mzero
  mplus xM yM = StateT $ \ s -> 
    runStateT xM s `mplus` runStateT yM s
