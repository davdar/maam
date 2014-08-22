module Lang.CPS.Analyses where

import FP
import MAAM
import Lang.CPS.Classes.Delta
import Lang.CPS.Syntax
import Lang.CPS.Instances.Delta
import Lang.CPS.Instances.Monads
import Lang.CPS.Semantics
import qualified FP.Pretty as P

actions :: [(String, Action RCall)]
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

concrete_SS :: Action RCall -> RCall -> Set (RCall, FSΣ Cδ Cμ)
concrete_SS = execCollectWith cδ Cμ fsm

concrete :: Action RCall -> RCall -> Store Cδ Cμ
concrete = (joins . cmap (fsσ . snd)) .: concrete_SS

hybridFS_SS :: KHybridμ -> Action RCall -> RCall -> Set (RCall, FSΣ Aδ KHybridμ)
hybridFS_SS μ = execCollectWith aδ μ fsm

hybridFS :: KHybridμ -> Action RCall -> RCall -> Store Aδ KHybridμ
hybridFS = (joins . cmap (fsσ . snd)) ..: hybridFS_SS

hybridFI_SS :: KHybridμ -> Action RCall -> RCall -> (Set (RCall, FIΣ KHybridμ), Store Aδ KHybridμ)
hybridFI_SS μ = execCollectWith aδ μ fim

hybridFI :: KHybridμ -> Action RCall -> RCall -> Store Aδ KHybridμ
hybridFI = snd ..: hybridFI_SS

all :: [(String, RCall -> Doc)]
all = 
  do
    (actionS, action) <- actions
    return ("concrete:" ++ actionS, pretty . concrete action)
  <+>
  do
    (actionS, action) <- actions
    b <- [True, False]
    (μS, μ) <- hybridμs
    if b
      then return ("abstract:FS" ++ μS ++ ":" ++ actionS, pretty . hybridFS μ action)
      else return ("abstract:FI" ++ μS ++ ":" ++ actionS, pretty . hybridFI μ action)

runAll :: RCall -> Doc
runAll r =  do
  P.heading "Program:"
  P.newline
  pretty r
  traverseOn all $ \ (n, f) -> do
    P.newline
    P.heading n
    P.newline
    f r
