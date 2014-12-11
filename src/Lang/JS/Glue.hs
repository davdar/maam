module Lang.JS.Glue where

import FP
import System.Directory
import Lang.JS.Syntax

main :: IO ()
main = do
  jsFiles <- map (("benchmarks/" ++) . fromChars) . filter (not . hidden) ^$ getDirectoryContents $ toChars "benchmarks"
  traverseOn jsFiles $ \ jsFile -> do
    e <- fromFile jsFile
    pprint e
  where
    hidden ('.':_) = True
    hidden _ = True
