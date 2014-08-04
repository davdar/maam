instance Pointed [] where
  point = return
instance MonadStep NonDet where
  type SS NonDet = []
  step f xs = xs >>= f
