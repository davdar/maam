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
  [ ( "naive" , none )
  , ( "gc"   , gc   )
  ]

hybridμs :: [(String, KHybridμ)]
hybridμs = 
  [ ( "0CFA"    , KHybridμ 0 0 )
  , ( "1oCFA"   , KHybridμ 1 0 )
  , ( "1kCFA"   , KHybridμ 0 1 )
  , ( "1o1kCFA" , KHybridμ 1 1 )
  ]

monads :: [(String, KHybridμ -> Action RCall -> RCall -> Store Aδ KHybridμ)]
monads =
  [ ( "FSPS" , hybridFSPS)
  , ( "FSPI" , hybridFSPI)
  , ( "FI"   , hybridFI)
  ]


concrete_SS :: Action RCall -> RCall -> Set (RCall, FSPSΣ Cδ Cμ)
concrete_SS = runFSPS_SS .: execCollectWith cδ Cμ fspsm

concrete :: Action RCall -> RCall -> Store Cδ Cμ
concrete = (joins . cmap (fspsσ . snd)) .: concrete_SS

hybridFSPS_SS :: KHybridμ -> Action RCall -> RCall -> Set (RCall, FSPSΣ Aδ KHybridμ)
hybridFSPS_SS μ = runFSPS_SS .: execCollectWith aδ μ fspsm

hybridFSPS :: KHybridμ -> Action RCall -> RCall -> Store Aδ KHybridμ
hybridFSPS = (joins . cmap (fspsσ . snd)) ..: hybridFSPS_SS

hybridFSPI_SS :: KHybridμ -> Action RCall -> RCall -> Set ((RCall, FSPIΣ KHybridμ), Store Aδ KHybridμ)
hybridFSPI_SS μ = runFSPI_SS .: execCollectWith aδ μ fspim

hybridFSPI :: KHybridμ -> Action RCall -> RCall -> Store Aδ KHybridμ
hybridFSPI = (joins . cmap snd) ..: hybridFSPI_SS

hybridFI_SS :: KHybridμ -> Action RCall -> RCall -> (Set (RCall, FIΣ KHybridμ), Store Aδ KHybridμ)
hybridFI_SS μ = runFI_SS .: execCollectWith aδ μ fim

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
    (monadS, monad) <- monads
    (μS, μ) <- hybridμs
    return $ (monadS ++ ":" ++ μS ++ ":" ++ actionS, pretty . monad μ action)

runEach :: [(String, RCall -> Doc)] -> RCall -> Doc
runEach cfgs r =  do
  P.heading "Program:"
  P.newline
  pretty r
  traverseOn cfgs $ \ (n, f) -> do
    P.newline
    P.heading n
    P.newline
    f r
