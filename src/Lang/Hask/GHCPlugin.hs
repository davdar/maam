{-# LANGUAGE CPP #-}

module Lang.Hask.GHCPlugin where

import FP
import UniqSupply
import Lang.Hask.CPS
import CoreMonad
import HscTypes
import qualified CoreSyn as H
import Lang.Hask.Compat
import Lang.Hask.Pretty ()
import Outputable
#if MIN_VERSION_base(4,8,0)
import Plugins
#endif

plugin :: Plugin
plugin = defaultPlugin |: installCoreToDosL =: \ (_ops :: [CommandLineOption]) (todo :: [CoreToDo]) -> do
    reinitializeGlobals
    df <- getDynFlags
    io $ initGlobalDynFlags df
    return $ todo ++ single (CoreDoPluginPass (toChars "MAAM-Analyze") maamAnalyze)

maamAnalyze :: ModGuts -> CoreM ModGuts
maamAnalyze = updateM mg_bindsL $ mapM $ \case
  H.NonRec x e -> do
    df <- getDynFlags
    io $ initGlobalDynFlags df
    io $ print $ fromChars $ showPpr df e
    us <- getUniqueSupplyM
    c <- runReaderT us $ cps e
    io $ pprint c
    return $ H.NonRec x e
  H.Rec xes -> return $ H.Rec xes
