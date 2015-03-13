module Lang.LamIf.Analyses where

import FP
import MAAM
import Lang.LamIf.Val
import Lang.LamIf.Semantics
import Lang.LamIf.Monads
import Lang.LamIf.CPS

-- These instances are defined in MAAM.Time
timeChoices :: [(String, ExTime)]
timeChoices =
  [ ("*" , ExTime (W :: UniTime Cτ)     )
  , ("1" , ExTime (W :: UniTime (Kτ 1)) )
  , ("0" , ExTime (W :: UniTime Zτ)     )
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
  [ ( "ps" , ExMonad (W :: UniMonad PSΣ PSΣ𝒫 PS) )
  , ( "fs" , ExMonad (W :: UniMonad FSΣ FSΣ𝒫 FS) )
  , ( "fi" , ExMonad (W :: UniMonad FIΣ FIΣ𝒫 FI) )
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
