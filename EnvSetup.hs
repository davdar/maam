{-# LANGUAGE NoRebindableSyntax, NoOverloadedStrings, ImplicitPrelude #-}

module Main where

import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Compiler
import Distribution.Verbosity
import Data.Maybe
import Language.Haskell.Extension
import System.IO
import Control.Monad

main :: IO ()
main = do
  p <- readPackageDescription silent "maam.cabal"
  let bi = libBuildInfo $ condTreeData $ fromJust $ condLibrary p
  -- EXTENSIONS --
  let extensions = catMaybes $ map enabledOnly $ defaultExtensions bi
  -- write out a file listing all extensions
  withFile ".extensions" WriteMode $ \ h -> do
    forM_ extensions $ \ e -> do
      hPutStrLn h $ show e
  -- write out a file for ghci to load extensions
  withFile ".extensions.ghci" WriteMode $ \ h -> do
    forM_ extensions $ \ e -> do
      hPutStrLn h $ ":set -X" ++ show e
  -- write out a file for hdevtools to load extensions
  withFile ".extensions.hdev" WriteMode $ \ h -> do
    forM_ extensions $ \ e -> do
      hPutStrLn h $ "-g-X" ++ show e
  -- OPTIONS --
  let ops = fromJust $ lookup GHC $ options bi
  -- write out a file for ghci to load options
  withFile ".ghc_options.ghci" WriteMode $ \ h -> do
    forM_ ops $ \ o -> do
      hPutStrLn h $ ":set " ++ o
  -- write out a file for hdevtools to load options
  withFile ".ghc_options.hdev" WriteMode $ \ h -> do
    forM_ ops $ \ o -> do
      hPutStrLn h $ "-g" ++ o
  return ()
  where
    enabledOnly (EnableExtension s) = Just s
    enabledOnly _ = Nothing
