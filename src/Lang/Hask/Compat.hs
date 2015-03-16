module Lang.Hask.Compat where

import FP
import CoreSyn hiding (Bind)
import CoreMonad
import HscTypes
import qualified Prelude
import Data.IORef
import DynFlags
import System.IO.Unsafe

makeLenses ''Plugin
makeLenses ''ModGuts
makePrisms ''AltCon

instance Functor CoreM where map = mmap
instance Unit CoreM where unit = Prelude.return
instance Product CoreM where (<*>) = mpair
instance Bind CoreM where (>>=) = (Prelude.>>=)
instance Applicative CoreM where (<@>) = mapply
instance Monad CoreM
instance MonadIO CoreM where io = CoreMonad.liftIO

{-# NOINLINE globalDynFlags #-}
globalDynFlags :: IORef DynFlags
globalDynFlags = unsafePerformIO $ newIORef $ error "uninitialized dyn flags"

initGlobalDynFlags :: DynFlags -> IO ()
initGlobalDynFlags = writeIORef globalDynFlags

dynFlags :: () -> DynFlags
dynFlags () = unsafePerformIO $ readIORef globalDynFlags
