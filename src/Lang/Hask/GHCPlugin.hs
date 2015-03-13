module Core2Sexp.Plugin (plugin) where

import FP
import GhcPlugins
import Control.Applicative

makeLenses ''Plugin

plugin :: Plugin
plugin = defaultPlugin |: 
  installCoreToDosL =: \ (_ops :: [CommandLineOption]) (todo :: [CoreToDo]) -> do
    reinitializeGlobals
    return $ todo ++ single (CoreDoPluginPass (toChars "MAAM-Analyze") maamAnalyze)

maamAnalyze :: ModGuts -> CoreM ModGuts
maamAnalyze mg = do
  undefined $ mg_binds mg
  return mg
