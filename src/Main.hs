module Main where

import FP
import MAAM ()
import Lang.CPS

p0 :: Call
p0 = 
  App (Lam ["f"] $ 
         App (Lam ["g"] $
                If (Var "b")
                  (App (Var "g") [LitA $ I 1, Lam ["x"] (Halt $ Var "x")])
                  (App (Var "f") [LitA $ I 1, Lam ["x"] (Halt $ Var "x")]))
             [ Lam ["x", "k"] $ 
                 App (Var "f") [Var "x", Lam ["y"] $ App (Var "k") [Var "y"]]])
      [ Lam ["x", "k"] $ 
          App (Var "k") [Var "x"] ]

main :: IO ()
main = print "<>"
