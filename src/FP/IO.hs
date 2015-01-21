module FP.IO where

import FP.Core
import qualified Data.Text.IO as T

readFile :: String -> IO String
readFile = T.readFile . toChars

writeFile :: String -> String -> IO ()
writeFile fn s = T.writeFile (toChars fn) s
