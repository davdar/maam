module FP.Console where

import FP.Core
import FP.Pretty
import FP.Free

leader :: String
leader = "\ESC["

sgrCloser :: String
sgrCloser = "m"

reset :: String
reset = "0"

fgCode :: Color256 -> String
fgCode = (++) "38;5;" . toString

bgCode :: Color256 -> String
bgCode = (++) "48;5;" . toString

ulCode :: String
ulCode = "4"

bdCode :: String
bdCode = "1"

applyFormat :: Format -> String -> String
applyFormat (Format fg bg ul bd) s = concat
  [ leader 
  , concat $ intersperse ";" $ msums
    [ useMaybe $ fgCode <$> fg
    , useMaybe $ bgCode <$> bg
    , guard ul >> return ulCode
    , guard bd >> return bdCode
    ]
  , sgrCloser
  , s
  , leader
  , reset
  , sgrCloser
  ]

formatChunk :: Chunk -> String
formatChunk (Text s) = s
formatChunk Newline = "\n"

formatOut :: Out -> String
formatOut (MonoidFunctorElem o) = formatChunk o
formatOut MFNull = ""
formatOut (o1 :+++: o2) = formatOut o1 ++ formatOut o2
formatOut (MFApply (fmt, o)) = applyFormat fmt $ formatOut o

noFormatOut :: Out -> String
noFormatOut (MonoidFunctorElem o) = formatChunk o
noFormatOut MFNull = ""
noFormatOut (o1 :+++: o2) = formatOut o1 ++ formatOut o2
noFormatOut (MFApply (_, o)) = formatOut o

pprint :: (Pretty a) => a -> IO ()
pprint = print . formatOut . execPretty0 . pretty

pprintWidth :: (Pretty a) => Int -> a -> IO ()
pprintWidth n = print . formatOut . execPretty0 . localSetL maxColumnWidthL n . pretty
