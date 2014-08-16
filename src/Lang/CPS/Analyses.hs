module Lang.CPS.Analyses where

import FP
import MAAM
import Lang.CPS.Classes.Delta
import Lang.CPS.Syntax
import Lang.CPS.Instances.Delta
import Lang.CPS.Instances.Monads
import Lang.CPS.Semantics

actions :: [(String, Action Call)]
actions = 
  [ ( "none" , none )
  , ( "gc"   , gc   )
  ]

hybridμs :: [(String, KHybridμ)]
hybridμs = 
  [ ( "0CFA"    , KHybridμ 0 0 )
  , ( "1oCFA"   , KHybridμ 1 0 )
  , ( "1kCFA"   , KHybridμ 0 1 )
  , ( "1o1kCFA" , KHybridμ 1 1 )
  ]

concrete_SS :: Action Call -> Call -> Set (Call, FSΣ Cδ Cμ)
concrete_SS = execCollectWith cδ Cμ fsm

concrete :: Action Call -> Call -> Store Cδ Cμ
concrete = (joins . cmap (fsσ . snd)) .: concrete_SS

hybridFS_SS :: KHybridμ -> Action Call -> Call -> Set (Call, FSΣ Aδ KHybridμ)
hybridFS_SS μ = execCollectWith aδ μ fsm

hybridFS :: KHybridμ -> Action Call -> Call -> Store Aδ KHybridμ
hybridFS = (joins . cmap (fsσ . snd)) ..: hybridFS_SS

hybridFI_SS :: KHybridμ -> Action Call -> Call -> (Set (Call, FIΣ KHybridμ), Store Aδ KHybridμ)
hybridFI_SS μ = execCollectWith aδ μ fim

hybridFI :: KHybridμ -> Action Call -> Call -> Store Aδ KHybridμ
hybridFI = snd ..: hybridFI_SS

instance ToString (Store δ μ) where
  toString = undefined

all :: [(String, Call -> String)]
all = 
  do
    (actionS, action) <- actions
    return ("concrete:" ++ actionS, toString . concrete action)
  <+>
  do
    (actionS, action) <- actions
    b <- [True, False]
    (μS, μ) <- hybridμs
    if b
      then return ("abstract:FS" ++ μS ++ ":" ++ actionS, toString . hybridFS μ action)
      else return ("abstract:FI" ++ μS ++ ":" ++ actionS, toString . hybridFI μ action)
