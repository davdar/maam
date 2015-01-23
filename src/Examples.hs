module Examples where

import Lang.Lam
import Lang.CPS
import FP
import qualified FP.Pretty as P
import MAAM
import Lang.Common

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


withOptions :: [(Doc, Options)] -> Exp -> Doc
withOptions os e =
  let (se, c) = stampCPS e
  in P.vsep
    [ P.heading "Source"
    , localSetL P.maxRibbonWidthL 40 $ pretty e 
    , P.heading "Stamped"
    , localSetL P.maxRibbonWidthL 40 $ pretty se
    , P.heading "CPS"
    , localSetL P.maxRibbonWidthL 40 $ pretty c
    , P.vsep $ mapOn os $ \ (info, o) -> 
        case runWithOptions o c of
          ExSigma ς -> P.vsep
            [ pretty info
            , pretty ς
            ]
    ]

examplesMain :: IO ()
examplesMain = do
  e <- parseFile "data/lam-src/simp1.lam"
  let os = 
        makeOptions
        ["*"]
        ["*"]
        ["concrete"]
        ["ps"]
        ["no"]
        ["link"]
        ["*"]
        ["*"]
        ++
        makeOptions
        ["0"]
        ["0"]
        ["abstract"]
        ["fi"]
        ["no"]
        ["link"]
        ["*"]
        ["*"]
  pprint $ withOptions os e

e1 :: CVal Cτ Cτ SGCall
e1 = op Add1 $ LitC $ I 1
