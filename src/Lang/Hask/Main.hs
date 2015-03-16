module Lang.Hask.Main where

import FP

import Lang.Hask.Execution
import Lang.Hask.Monads
import Lang.Hask.Time
import Lang.Hask.ValConcrete
import Lang.Hask.CPS
import Lang.Hask.SumOfProdVal
import System.IO
import Var
import Literal

import qualified CoreSyn as H

main :: IO ()
main = do
  loop $ execDiffs (psm (P :: P (Zτ Int)) (P :: P (Zτ Int)) (P :: P (SumOfProdVal OCVal))) undefined
  where
    loop :: [PSΣ𝒫 (SumOfProdVal OCVal) (Zτ Int) (Zτ Int) Call] -> IO ()
    loop [] = return ()
    loop (x:xs) = do
      let loopInput = do
            c <- getChar
            case c of
              ' ' -> do
                pprint x
                loop xs
              'q' -> return ()
              _ -> loopInput
      loopInput
