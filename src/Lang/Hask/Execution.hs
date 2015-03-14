module Lang.Hask.Execution where

import FP

import Lang.Hask.Semantics
import MAAM
import Lang.Hask.CPS

class (PartialOrder (ς Call), Join (ς Call), Bot (ς Call), Inject ς, MonadStep ς m) => Execution ς m | m -> ς

exec :: forall ς ν lτ dτ m. (Analysis ν lτ dτ m, Execution ς m) => P m -> Call -> ς Call
exec P c = collect (mstepγ (call :: Call -> m Call)) $ inj c
