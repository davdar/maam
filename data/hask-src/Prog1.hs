{-# OPTIONS_GHC -fplugin=Lang.Hask.GHCPlugin #-}

module Prog1 where

import Prelude

p :: Int
p = 1

id :: a -> a
id x = x

app :: (a -> a) -> a -> a
app f x = f x

app2 :: (a -> a) -> a -> a
app2 f x = f (f x)

compose :: (b -> c) -> (a -> b) -> a -> c
compose g f x = g (f x)
