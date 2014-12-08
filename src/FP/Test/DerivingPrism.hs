module FP.Test.DerivingPrism where

import FP

data Foo a b = Fooey a Int | Bary Bool b Bool
makePrisms ''Foo

x :: Foo String Int
x = Fooey "hi" 1

y :: Foo String Int
y = Bary True 2 False
