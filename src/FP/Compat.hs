{-# LANGUAGE OverlappingInstances #-}

module FP.Compat where

import FP.Core
import qualified Prelude

instance (Monad m) => Prelude.Monad m where { return = FP.Core.return ; (>>=) = (FP.Core.>>=) }
