module Main where

import FP
import System.Directory
import Lang.JS.FrontEnd
import Lang.JS.Execution
import Lang.JS.Syntax

filesFromDirM :: String -> IO [String]
filesFromDirM dir =
  map (((dir ++ "/") ++) . fromChars) . filter (not . hidden) ^$ getDirectoryContents $ toChars dir
  where
    hidden ('.':_) = True
    hidden _ = False

js :: Exp 
js = Fix $ Var $ Name "x"

main :: IO ()
main = do
  jsFiles <- filesFromDirM "tinytests"
  traverseOn jsFiles $ \ jsFile -> do
    e <- fromFile jsFile
    --pprint $ execM e
    pprint e
