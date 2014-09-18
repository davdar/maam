instance (JoinLatticeF m) => MonadPlus (NonDetT m) where
  mzero = NonDetT mzero
  mplus xM yM = case joinLatticeF :: JoinLatticeW (m [a]) of
    JoinLatticeW -> runNondetT xM \/ runNonDetT yM
