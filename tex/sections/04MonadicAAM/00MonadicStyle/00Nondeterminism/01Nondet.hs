type Nondet = []
instance Monad Nondet where
  return x = [x]
  [] >>= k = []
  (x:xs) >>= k = k x ++ (xs >>= k)
