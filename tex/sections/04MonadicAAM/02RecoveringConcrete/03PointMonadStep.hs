instance Pointed Point where
  point = Point
instance MonadStep Point where
  type SS Point = Point
  step f xs = xs >>= f
