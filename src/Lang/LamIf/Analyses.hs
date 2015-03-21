module Lang.LamIf.Analyses where

import FP
import MAAM
import Lang.LamIf.Val
import Lang.LamIf.Semantics
import Lang.LamIf.Monads
import Lang.LamIf.CPS
import Lang.LamIf.StateSpace

-- These instances are defined in MAAM.Time
timeChoices :: [(String, ExTime)]
timeChoices =
  [ ("*" , ExTime (W :: UniTime (Cτ Ψ))     )
  , ("1" , ExTime (W :: UniTime (Kτ 1 Ψ)) )
  , ("0" , ExTime (W :: UniTime (Zτ Ψ))     )
  ]

-- These instances are defined in Lang.CPS.Val
valChoices :: [(String, ExVal)]
valChoices =
  [ ( "concrete" , ExVal (W :: UniVal (Power CVal)) )
  , ( "abstract" , ExVal (W :: UniVal (Power AVal)) )
  ]

-- These instances are defined in MAAM.MonadStep and Lang.CPS.Monads
monadChoices :: [(String, ExMonad)]
monadChoices =
  [ ( "ps" , ExMonad (W :: UniMonad PSΣ PSΣ𝒫 PS) $ pretty . map (setMap (mapSnd 𝓈σ) . unPSΣ𝒫) )
  , ( "fs" , ExMonad (W :: UniMonad FSΣ FSΣ𝒫 FS) $ 
               pretty . map (filter ((/= bot) . snd) . map (\ (a, (_, σ)) -> (a, mapFilter (/= bot) σ)) . toList . unFSΣ𝒫) )
  , ( "fi" , ExMonad (W :: UniMonad FIΣ FIΣ𝒫 FI) $ pretty . joins . map (snd . unFIΣ𝒫) )
  ]

-- These are defined in Lang.CPS.Semantics
gcChoices :: [(String, AllGC)]
gcChoices = 
  [ ( "no"  , AllGC nogc  )
  , ( "yes" , AllGC yesgc )
  ]

-- These are defined in Lang.CPS.Semantics
closureChoices :: [(String, AllCreateClo)]
closureChoices =
  [ ( "link" , AllCreateClo linkClo )
  , ( "copy" , AllCreateClo copyClo )
  ]

timeFilterChoices :: [(String, TimeFilter)]
timeFilterChoices =
  [ ("*"   , not . is haltL . stampedFix )
  , ("app" , is appFL . stampedFix )
  ]
