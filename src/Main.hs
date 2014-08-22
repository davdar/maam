module Main where

import FP
import MAAM ()
import Lang.CPS

p0 :: SCall
p0 = 
  ( letAtom "f" 
      (lam "x" "k" $ v "k" @# v "x") 
  $ letAtom "g" 
      (lam "x" "k" 
         $ letApp "y" (v "f") (v "x") 
         $ v "k" @# v "y")
  $ ifc true
      ( letApp "x" (v "g") (int 1) 
      $ halt $ v "x")
      ( letApp "x" (v "f") (int 1) 
      $ halt $ v "x"))

main :: IO ()
main = print "<>"
