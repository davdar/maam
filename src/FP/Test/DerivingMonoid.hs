module FP.Test.DerivingPrism where

import FP

data Foo a b = Foo
  { field1 :: Int
  , field2 :: String
  , field3 :: (a, b)
  }
makeMonoid ''Foo

x :: Foo Int String
x = Foo 1 "hi" (2, "there")

y :: Foo Int String
y = Foo 100 "X" (200, "Y")

xy :: Foo Int String
xy = x ++ y
