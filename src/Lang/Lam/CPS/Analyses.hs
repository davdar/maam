module Lang.Lam.CPS.Analyses where

import FP
import MAAM
import Lang.Lam.CPS.Classes.Delta
import Lang.Lam.CPS.Syntax
import Lang.Lam.CPS.Instances.Delta
import Lang.Lam.CPS.Instances.Monads
import Lang.Lam.CPS.MonadicSemantics
import qualified FP.Pretty as P
import Lang.Lam.Syntax (SGName)

actions :: [(String, Action (Call SGName))]
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

monads :: [(String, KHybridμ -> Action (Call SGName) -> (Call SGName) -> Store Aδ KHybridμ)]
monads =
  [ ( "FSPS" , hybridFSPS)
  , ( "FSPI" , hybridFSPI)
  , ( "FI"   , hybridFI)
  ]


concrete_SS :: Action (Call SGName) -> (Call SGName) -> Set ((Call SGName), FSPSΣ Cδ Cμ)
concrete_SS = runFSPS_SS .: execCollectWith cδ Cμ fspsm

concrete :: Action (Call SGName) -> (Call SGName) -> Store Cδ Cμ
concrete = (joins . cmap (fspsσ . snd)) .: concrete_SS

hybridFSPS_SS :: KHybridμ -> Action (Call SGName) -> (Call SGName) -> Set ((Call SGName), FSPSΣ Aδ KHybridμ)
hybridFSPS_SS μ = runFSPS_SS .: execCollectWith aδ μ fspsm

hybridFSPS :: KHybridμ -> Action (Call SGName) -> (Call SGName) -> Store Aδ KHybridμ
hybridFSPS = (joins . cmap (fspsσ . snd)) ..: hybridFSPS_SS

hybridFSPI_SS :: KHybridμ -> Action (Call SGName) -> (Call SGName) -> Set (((Call SGName), FSPIΣ KHybridμ), Store Aδ KHybridμ)
hybridFSPI_SS μ = runFSPI_SS .: execCollectWith aδ μ fspim

hybridFSPI :: KHybridμ -> Action (Call SGName) -> (Call SGName) -> Store Aδ KHybridμ
hybridFSPI = (joins . cmap snd) ..: hybridFSPI_SS

hybridFI_SS :: KHybridμ -> Action (Call SGName) -> (Call SGName) -> (Set ((Call SGName), FIΣ KHybridμ), Store Aδ KHybridμ)
hybridFI_SS μ = runFI_SS .: execCollectWith aδ μ fim

hybridFI :: KHybridμ -> Action (Call SGName) -> (Call SGName) -> Store Aδ KHybridμ
hybridFI = snd ..: hybridFI_SS

all :: [(String, (Call SGName) -> Doc)]
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

runEach :: [(String, (Call SGName) -> Doc)] -> (Call SGName) -> Doc
runEach cfgs r =  do
  P.heading "Program:"
  P.newline
  pretty r
  traverseOn cfgs $ \ (n, f) -> do
    P.newline
    P.heading n
    P.newline
    f r
