type Semantics d aam m =
  ( Delta d
  , AAM aam
  , Monad m
  , MonadPlus m
  , MonadState (E aam) m
  , MonadState (S d aam) m
  , MonadState (T aam) m
  )
