module Lang.LamIf.Examples where

import Lang.LamIf
import FP
import qualified FP.Pretty as P

examplesMain :: IO ()
examplesMain = flowSensitivityMain

makeOptions :: [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [(Doc, Options)]
makeOptions ltime dtime val monad gc closure lfilter dfilter = do
  lt <- ltime
  dt <- dtime
  v <- val
  m <- monad
  g <- gc
  c <- closure
  lf <- lfilter
  df <- dfilter
  let d = P.hsep $ map P.heading
        [ concat [ "LT=", lt ]
        , concat [ "DT=", dt ]
        , concat [ "V=", v ]
        , concat [ "M=", m ]
        , concat [ "G=", g ]
        , concat [ "C=", c ]
        , concat [ "LF=", lf ]
        , concat [ "DF=", df ]
        ]
      o = Options (timeChoices       #! lt) 
                  (timeChoices       #! dt) 
                  (valChoices        #! v ) 
                  (monadChoices      #! m ) 
                  (gcChoices         #! g ) 
                  (closureChoices    #! c ) 
                  (timeFilterChoices #! lf)
                  (timeFilterChoices #! df)
  return (d, o)


runOptions :: [(Doc, Options)] -> RawExp -> Doc
runOptions os e =
  let (se, c) = stampCPS e
  in P.vsep
    [ P.heading "Source"
    , localSetL P.maxRibbonWidthL 40 $ pretty e 
    , P.heading "Stamped"
    , localSetL P.maxRibbonWidthL 40 $ pretty se
    , P.heading "CPS"
    , localSetL P.maxRibbonWidthL 40 $ pretty c
    , P.vsep $ mapOn os $ \ (info, o) -> withOptions o $ \ gc cc ltf dtf ->
        let ς = execOnlyStuck gc cc ltf dtf c
        in P.vsep
            [ pretty info
            , pretty ς
            ]
    ]

flowSensitivityMain :: IO ()
flowSensitivityMain = do
  e <- parseFile "data/lamif-src/flow-sensitivity.lam"
  let os = makeOptions ["0"] ["0"] ["abstract"] ["fi", "fs", "ps"] ["yes"] ["link"] ["app"] ["app"]
  pprint $ runOptions os e

callSiteSensitivityMain :: IO ()
callSiteSensitivityMain = do
  e <- parseFile "data/lamif-src/call-site-sensitivity.lam"
  let os = makeOptions ["0"] ["0", "1"] ["abstract"] ["fi"] ["yes"] ["link"] ["app"] ["app"]
  pprint $ runOptions os e

objectSensitivityMain :: IO ()
objectSensitivityMain = do
  e <- parseFile "data/lamif-src/object-sensitivity.lam"
  let os = makeOptions ["0", "1"] ["0"] ["abstract"] ["fi"] ["yes"] ["link"] ["app"] ["app"]
  pprint $ runOptions os e
