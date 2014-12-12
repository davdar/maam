module Lang.JS.Main where

import FP
import System.Directory
import Lang.JS.FrontEnd
import Lang.JS.Execution

filesFromDirM :: String -> IO [String]
filesFromDirM dir =
  map (((dir ++ "/") ++) . fromChars) . filter (not . hidden) ^$ getDirectoryContents $ toChars dir
  where
    hidden ('.':_) = True
    hidden _ = False

js_main :: IO ()
js_main = do
  jsFiles <- filesFromDirM "tinytests"
  traverseOn jsFiles $ \ jsFile -> do
    e <- fromFile jsFile
    pprint $ execM e
