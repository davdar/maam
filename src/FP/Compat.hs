{-# LANGUAGE CPP #-}
{-# LANGUAGE OverlappingInstances #-}

module FP.Compat where

import FP.Core
import qualified Prelude

instance (Monad m) => Prelude.Monad m where { return = FP.Core.return ; (>>=) = (FP.Core.>>=) }

#if MIN_VERSION_base(4,8,0)
instance (Applicative f) => Prelude.Applicative f where { pure = FP.Core.pure ; (<*>) = (FP.Core.<@>) }

instance (Functor f) => Prelude.Functor f where { fmap = FP.Core.map }
#endif
