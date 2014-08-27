module Lang.Lam.Analyses where

import FP
import MAAM
import Lang.Lam.CPS.Classes.Delta
import Lang.Lam.CPS.Syntax
import Lang.Lam.CPS.Instances.Delta
import Lang.Lam.CPS.Instances.Monads
import Lang.Lam.CPS.MonadicSemantics
import qualified FP.Pretty as P

allActions :: [(String, Action SGCall)]
allActions = 
  [ ( "naive" , naive )
  , ( "gc"    , gc    )
  ]

allμs :: [(String, KHybridμ)]
allμs = 
  [ ( "0-cfa"    , KHybridμ 0 0 )
  , ( "1o-cfa"   , KHybridμ 1 0 )
  , ( "1k-cfa"   , KHybridμ 0 1 )
  , ( "1o-1k-CFA" , KHybridμ 1 1 )
  ]

allMonads :: [(String, KHybridμ -> Action SGCall -> SGCall -> Store Aδ KHybridμ)]
allMonads =
  [ ( "fsps" , fsps)
  , ( "fspi" , fspi)
  , ( "fi"   , fi)
  ]


concrete_SS :: Action SGCall -> SGCall -> Set (SGCall, FSPSΣ Cδ Cμ)
concrete_SS = runFSPS_SS .: execCollectWith cδ Cμ fspsm

concrete :: Action SGCall -> SGCall -> Store Cδ Cμ
concrete = (joins . cmap (fspsσ . snd)) .: concrete_SS

fsps_SS :: KHybridμ -> Action SGCall -> SGCall -> Set (SGCall, FSPSΣ Aδ KHybridμ)
fsps_SS μ = runFSPS_SS .: execCollectWith aδ μ fspsm

fsps :: KHybridμ -> Action SGCall -> SGCall -> Store Aδ KHybridμ
fsps = (joins . cmap (fspsσ . snd)) ..: fsps_SS

fspi_SS :: KHybridμ -> Action SGCall -> SGCall -> Set ((SGCall, FSPIΣ KHybridμ), Store Aδ KHybridμ)
fspi_SS μ = runFSPI_SS .: execCollectWith aδ μ fspim

fspi :: KHybridμ -> Action SGCall -> SGCall -> Store Aδ KHybridμ
fspi = (joins . cmap snd) ..: fspi_SS

fi_SS :: KHybridμ -> Action SGCall -> SGCall -> (Set (SGCall, FIΣ KHybridμ), Store Aδ KHybridμ)
fi_SS μ = runFI_SS .: execCollectWith aδ μ fim

fi :: KHybridμ -> Action SGCall -> SGCall -> Store Aδ KHybridμ
fi = snd ..: fi_SS

allP :: (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> [(String, SGCall -> Doc)]
allP modeP actionP μP monadP = 
  do
    guard $ modeP "concrete"
    (actionS, action) <- allActions
    guard $ actionP actionS
    return ("concrete:" ++ actionS, pretty . concrete action)
  <+>
  do
    guard $ modeP "abstract" 
    (actionS, action) <- allActions
    guard $ actionP actionS
    (monadS, monad) <- allMonads
    guard $ monadP monadS
    (μS, μ) <- allμs
    guard $ μP μS
    return $ (monadS ++ ":" ++ μS ++ ":" ++ actionS, pretty . monad μ action)

all :: [(String, SGCall -> Doc)]
all = allP top top top top

allE :: [String] -> [String] -> [String] -> [String] -> [(String, SGCall -> Doc)]
allE modes actions μs monads = allP (elemOf modes) (elemOf actions) (elemOf μs) (elemOf monads)

runEachOn :: SGCall -> [(String, SGCall -> Doc)] -> Doc
runEachOn r cfgs = P.vsep $ mapOn cfgs $ \ (n, f) -> P.vsep
    [ P.heading n
    , f r
    ]
