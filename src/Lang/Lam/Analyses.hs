module Lang.Lam.Analyses where

import FP
import MAAM
import Lang.Lam.CPS.Classes.Delta
import Lang.Lam.CPS.Syntax
import Lang.Lam.CPS.Instances.Delta
import Lang.Lam.CPS.Instances.Monads
import Lang.Lam.CPS.MonadicSemantics

allGCs :: [(String, PolyGC)]
allGCs = 
  [ ( "no"  , nogc  )
  , ( "yes" , yesgc )
  ]

allCreateClos :: [(String, PolyCreateClo)]
allCreateClos =
  [ ( "link" , linkClo )
  , ( "copy" , copyClo )
  ]

allTimeFilters :: [(String, SGCall -> Bool)]
allTimeFilters =
  [ ("location" , const True )
  , ("app"      , isAppF     )
  -- , ("lambda"   , isLamF     )
  ]

allμs :: [(String, KHybridμ)]
allμs = 
  [ ( "0-cfa"     , KHybridμ 0 0 )
  , ( "1k-cfa"    , KHybridμ 0 1 )
  , ( "1o-cfa"    , KHybridμ 1 0 )
  , ( "1k-1o-CFA" , KHybridμ 1 1 )
  ]

-- control sensitivity?
allMonads :: [(String, KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Store Aδ KHybridμ)]
allMonads =
  [ ( "fsps" , fsps)
  , ( "fspi" , fspi)
  , ( "fi"   , fi)
  ]

concrete_SS :: PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Set (SGCall, FSPSΣ Cδ Cμ)
concrete_SS gc createClo timeFilter = runFSPS_SS . execCollect cδ Cμ fspsm gc createClo timeFilter

concrete :: PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Store Cδ Cμ
concrete = (joins . cmap (fspsσ . snd)) ...: concrete_SS

fsps_SS :: KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Set (SGCall, FSPSΣ Aδ KHybridμ)
fsps_SS μ gc createClo timeFilter = runFSPS_SS . execCollect aδ μ fspsm gc createClo timeFilter

fsps :: KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Store Aδ KHybridμ
fsps = (joins . cmap (fspsσ . snd)) ....: fsps_SS

fspi_SS :: KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Set ((SGCall, FSPIΣ KHybridμ), Store Aδ KHybridμ)
fspi_SS μ gc createClo timeFilter = runFSPI_SS . execCollect aδ μ fspim gc createClo timeFilter

fspi :: KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Store Aδ KHybridμ
fspi = (joins . cmap snd) ....: fspi_SS

fi_SS :: KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> (Set (SGCall, FIΣ KHybridμ), Store Aδ KHybridμ)
fi_SS μ gc createClo timeFilter = runFI_SS . execCollect aδ μ fim gc createClo timeFilter

fi :: KHybridμ -> PolyGC -> PolyCreateClo -> TimeFilter -> SGCall -> Store Aδ KHybridμ
fi = snd ....: fi_SS

allP :: (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> (String -> Bool) -> [(String, SGCall -> Doc)]
allP modeP gcP createCloP lexTimeFilterP dynTimeFilterP μP monadP = 
  do
    guard $ modeP "concrete"
    (gcS, gc) <- allGCs
    guard $ gcP gcS
    (createCloS, createClo) <- allCreateClos
    guard $ createCloP createCloS
    (lexTimeFilterS, lexTimeFilter) <- allTimeFilters
    guard $ lexTimeFilterP lexTimeFilterS
    (dynTimeFilterS, dynTimeFilter) <- allTimeFilters
    guard $ dynTimeFilterP dynTimeFilterS
    let msg = concat $ intersperse " "
          [ "<concrete>"
          , "<gc=" ++ gcS ++ ">"
          , "<createClo=" ++ createCloS ++ ">"
          , "<lexTimeFilter=" ++ lexTimeFilterS ++ ">"
          , "<dynTimeFilter=" ++ dynTimeFilterS ++ ">"
          ]
    return (msg, pretty . concrete gc createClo (TimeFilter lexTimeFilter dynTimeFilter))
  <++>
  do
    guard $ modeP "abstract" 
    (gcS, gc) <- allGCs
    guard $ gcP gcS
    (createCloS, createClo) <- allCreateClos
    guard $ createCloP createCloS
    (lexTimeFilterS, lexTimeFilter) <- allTimeFilters
    guard $ lexTimeFilterP lexTimeFilterS
    (dynTimeFilterS, dynTimeFilter) <- allTimeFilters
    guard $ dynTimeFilterP dynTimeFilterS
    (μS, μ) <- allμs
    guard $ μP μS
    (monadS, monad) <- allMonads
    guard $ monadP monadS
    let msg = concat $ intersperse " "
          [ "<abstract>"
          , "<gc=" ++ gcS ++ ">"
          , "<createClo=" ++ createCloS ++ ">"
          , "<lexTimeFilter=" ++ lexTimeFilterS ++ ">"
          , "<dynTimeFilter=" ++ dynTimeFilterS ++ ">"
          , "<μ=" ++ μS ++ ">"
          , "<monad=" ++ monadS ++ ">"
          ]
    return (msg, pretty . monad μ gc createClo (TimeFilter lexTimeFilter dynTimeFilter))

all :: [(String, SGCall -> Doc)]
all = allP top top top top top top top

allE :: [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [String] -> [(String, SGCall -> Doc)]
allE modes gcs createClos lexTimeFilters dynTimeFilters μs monads = allP (elemOf modes) (elemOf gcs) (elemOf createClos) (elemOf lexTimeFilters) (elemOf dynTimeFilters) (elemOf μs) (elemOf monads)
