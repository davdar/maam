instance MonadPlus Point where
  mzero = Bot
  mplus Bot yM = yM
  mplus xM Bot = xM
  mplus Top yM = Top
  mplus xM Top = Top
  mplus (Point x) (Point y) = Top
