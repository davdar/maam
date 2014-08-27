module Lang.Lam.Examples where

import Lang.Lam.Syntax
import FP
import qualified FP.Pretty as P
import qualified Lang.Lam.Analyses as A
import Lang.Lam.Passes.B_CPSConvert

doConfig :: Exp -> [String] -> [String] -> [String] -> [String] -> Doc
doConfig e modes actions μs monads =
  let (se, c) = stampCPS e
  in P.vsep
    [ P.heading "Source"
    , pretty e 
    , P.heading "Stamped"
    , pretty se
    , P.heading "CPS"
    , pretty c
    , A.runEachOn c $ A.allE modes actions μs monads
    ]

-- Simple KCFA {{{

simpleKCFA :: Exp
simpleKCFA = 
  llet "id" (lam "x" $ v "x") $
  iif someBool
    (v "id" $# int 1)
    (v "id" $# int 2)

doSimpleKCFA :: Doc
doSimpleKCFA = doConfig simpleKCFA ["concrete, abstract"] ["naive"] ["0-cfa", "1k-cfa"] ["fi"]

-- }}}

simpleMCFA :: Exp
simpleMCFA =
  llet "g" (lam "x" $ -- lam "y" $
    iif (v "x" {- /\# v "y" -}) (int 100) (int 200)) $
  -- llet "ff" (lam "f" $ v "f" @# int 1) $
  iif (bool True)
    (v "g" @# int 2) -- @# int 1)
    (v "g" @# int 3) -- @# int 1)
    -- (v "ff" $# v "g" @# int 2 @# int 1)
    -- (v "ff" $# v "g" @# int (-2) @# int 1)

exampleMain :: IO ()
exampleMain =
  pprint $ P.vsep
    [ return ()
    -- , doSimpleKCFA
    , doConfig simpleMCFA ["abstract"] ["naive"] ["0-cfa"] ["fi"]
    ]
