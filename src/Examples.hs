module Examples where

import Lang.Lam.Syntax
import FP
import qualified FP.Pretty as P
import qualified Lang.Lam.Analyses as A
import Lang.Lam.Passes.B_CPSConvert

formatResults :: Doc -> Doc
formatResults = localSetL P.maxColumnWidthL 120 . localSetL P.maxRibbonWidthL 120

doConfig :: Exp -> [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> Doc
doConfig e modes gcs createClosures lexTimeFilter dynTimeFilter μs monads =
  let (se, c) = stampCPS e
  in P.vsep
    [ P.heading "Source"
    , localSetL P.maxRibbonWidthL 40 $ pretty e 
    , P.heading "Stamped"
    , localSetL P.maxRibbonWidthL 40 $ pretty se
    , P.heading "CPS"
    , localSetL P.maxRibbonWidthL 40 $ pretty c
    , P.vsep $ mapOn (A.allE modes gcs createClosures lexTimeFilter dynTimeFilter μs monads) $ uncurry $ \ n f -> P.vsep
        [ P.heading n
        , formatResults $ f c
        ]
    ]

simpleKCFA :: Exp
simpleKCFA = 
  llet "id" (lam "x" $ v "x") $
  iif someBool
    (v "id" $# int 1)
    (v "id" $# int 2)

simpleMCFA :: Exp
simpleMCFA =
  llet "g" (lam "x" $ lam "y" $
    iif (gez (v "x")) (int 100) (int 200)) $
  llet "ff" (lam "f" $ v "f" @# int 0) $
  iif someBool
    (v "ff" $# v "g" @# int 1)
    (v "ff" $# v "g" @# int (-1))

simpleLexicalTime :: Exp
simpleLexicalTime =
  llet "ff" (lam "f" $ lam "x" $ v "f" @# v "x") $
  llet "g" (lam "x" $ gez $ v "x") $
  llet "h" (lam "x" $ gez $ v "x") $
  iif someBool
    (v "ff" @# v "g" @# int 1)
    (v "ff" @# v "h" @# int (-1))

examplesMain :: IO ()
examplesMain =
  pprint $ P.vsep
    [ return ()
    -- , doConfig simpleKCFA        ["abstract"] ["no"] ["link"]         ["location"] ["location"] ["0-cfa", "1k-cfa"]  ["fi"]
    -- , doConfig simpleMCFA        ["abstract"] ["no"] ["link", "copy"] ["location"] ["location"] ["1k-cfa"]           ["fi"]
    , doConfig simpleLexicalTime ["abstract"] ["no"] ["link"]         ["app"]   ["app"]      ["1k-cfa", "1o-cfa"] ["fi"]
    ]
