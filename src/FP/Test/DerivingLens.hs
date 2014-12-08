module FP.Test.DerivingPrism where

import FP
 
data Foo a b = Foo
  { fooness :: (Int, a)
  , barness :: (Bool, b, Bool)
  }
makeLenses ''Foo

x :: Foo String Int
x = Foo (1, "hi") (True, 2, False)
