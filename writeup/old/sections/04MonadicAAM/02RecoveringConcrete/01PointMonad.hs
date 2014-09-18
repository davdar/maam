instance Monad Point where
  return = Point
  Top >>= k = Top
  Bot >>= k = Bot
  Point a >>= k = k a
