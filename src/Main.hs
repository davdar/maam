module Main where

import FP
import Lang.Lam
import qualified FP.Pretty as P

p0 :: Exp
p0 = 
  llet "id" (lam "x" $ v "x") $
  v "id" @# int 1

main :: IO ()
main = do
  let (e, c) = stampCPS p0
  pprint $ do
    P.heading "Direct Style"
    pretty e
    P.newline >> P.heading "CPS"
    pretty c
    
