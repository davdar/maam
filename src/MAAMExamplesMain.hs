module Main where

import FP
import Lang.LamIf.Examples
import Lang.LamIf.Parser

main ∷ IO ()
main = do
  e ← e_2
  pprint $ ppHeader "program"
  pprint $ displaySourceContext $ sourceExpContext e
  pprint $ ppHeader "zcfa flow insensitive"
  zcfa_FI
  pprint $ ppHeader "zcfa flow sensitive"
  zcfa_FS
  pprint $ ppHeader "zcfa path sensitive"
  zcfa_PS
  
