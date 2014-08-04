instance (JoinLatticeF m) => Monad (NonDetT m) where
  return x = NonDetT $ return [x]
  xM >>= k = case joinLatticeF :: JoinLatticeW (m [b]) of
    JoinLatticeW -> do
      xs <- runNondetT xM
      listJoin $ map (runNonDetT . k) xs
