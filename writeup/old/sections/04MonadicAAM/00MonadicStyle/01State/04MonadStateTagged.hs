class MonadStateTagged s m where
  type Cell s :: *
  get :: s -> m (Cell s)
  put :: s -> Cell s -> m ()

