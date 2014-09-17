instance (Pointed m) => Pointed (NondetT m) where
  point x = NondetT $ point [x]
instance (MonadStep m) => MonadStep (NondetT m) where
  type SS (NondetT m) = NondetT m
  step (f :: a -> NondetT m b) xM = 
    NondetT $ 
    step (\ xs -> runNondetT $ NondetT (return xs) >>= f) $ 
    runNondetT xM
