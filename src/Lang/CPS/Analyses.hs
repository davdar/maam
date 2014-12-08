module Lang.CPS.Analyses where

import FP
import MAAM
import Lang.CPS.Val
import Lang.CPS.Semantics
import Lang.CPS.Monads
import Lang.CPS.Syntax

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
  [ ( "concrete" , ExVal (W :: UniVal PCVal) )
  , ( "abstract" , ExVal (W :: UniVal PAVal) )
  ]

-- These instances are defined in MAAM.MonadStep and Lang.CPS.Monads
monadChoices :: [(String, ExMonad)]
monadChoices =
  [ ( "fsps" , ExMonad (W :: UniMonad PSΣ FSPSς FSPS) )
  , ( "fspi" , ExMonad (W :: UniMonad PIΣ FSPIς FSPI) )
  , ( "fipi" , ExMonad (W :: UniMonad PIΣ FIPIς FIPI) )
  ]

-- These are defined in Lang.CPS.Semantics
gcChoices :: [(String, AllGC)]
gcChoices = 
  [ ( "no"  , nogc  )
  , ( "yes" , yesgc )
  ]

-- These are defined in Lang.CPS.Semantics
closureChoices :: [(String, AllCreateClo)]
closureChoices =
  [ ( "link" , linkClo )
  , ( "copy" , copyClo )
  ]

timeFilterChoices :: [(String, TimeFilter)]
timeFilterChoices =
  [ ("*"   , const True             )
  , ("app" , isL appFL . stampedFix )
  ]
