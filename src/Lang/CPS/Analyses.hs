module Lang.CPS.Analyses where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta
import Lang.CPS.Instances.Delta
import Lang.CPS.Semantics

data FSΣ δ μ = FSΣ
  { fsρ :: Env μ
  , fslτ :: LexicalTime μ Ψ
  , fsσ :: Store δ μ
  , fsdτ :: DynamicTime μ Ψ
  }
newtype FlowSensitive δ μ a = FlowSensitive { runFlowSensitive :: StateT (FSΣ δ μ) (ListSetT ID) a }
  deriving 
    ( Unit, Functor, Applicative, Monad
    , MonadZero
    , MonadPlus
    , MonadStateI (FSΣ δ μ), MonadStateE (FSΣ δ μ), MonadState (FSΣ δ μ)
    )
-- TODO: MonadState instances for lenses

data FIΣ μ = FIΣ
  { fiρ :: Env μ
  , filτ :: LexicalTime μ Ψ
  , fidτ :: DynamicTime μ Ψ
  }
newtype FlowInsensitive δ μ a = FlowInsensitive { runFlowInsensitive :: StateT (FIΣ μ) (ListSetT (StateT (Store δ μ) ID)) a }
  deriving
    ( Unit, Functor, Applicative, Monad
    , MonadZero
    , MonadPlus
    , MonadStateI (FIΣ μ), MonadStateE (FIΣ μ), MonadState (FIΣ μ)
    )
-- TODO: MonadState instances for lenses and lifted from Store

--------------
-- Concrete --
--------------

concrete :: Call -> Set (Call, Env Cμ, LexicalTime Cμ Ψ, Store Cδ Cμ, DynamicTime Cμ Ψ)
concrete = _

concrete_gc :: Call -> Set (Call, Env Cμ, LexicalTime Cμ Ψ, Store Cδ Cμ, DynamicTime Cμ Ψ)
concrete_gc = _

------------
-- ko-cfa --
------------

fs_hybridCFA :: Int -> Int -> Call -> Set (Call, Env KHybridμ, LexicalTime KHybridμ Ψ, Store Aδ KHybridμ, DynamicTime KHybridμ Ψ)
fs_hybridCFA k o = _

fs_hybridCFA_gc :: Int -> Int -> Call -> Set (Call, Env KHybridμ, LexicalTime KHybridμ Ψ, Store Aδ KHybridμ, DynamicTime KHybridμ Ψ)
fs_hybridCFA_gc k o = _

fi_hybridCFA :: Int -> Call -> (Set (Call, Env KHybridμ, LexicalTime KHybridμ Ψ, DynamicTime KHybridμ Ψ), Store Aδ KHybridμ)
fi_hybridCFA k o = _

fi_hybridCFA_gc :: Int -> Call -> (Set (Call, Env KHybridμ, LexicalTime KHybridμ Ψ, DynamicTime KHybridμ Ψ), Store Aδ KHybridμ)
fi_hybridCFA_gc k o = _
