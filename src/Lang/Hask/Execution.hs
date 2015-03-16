module Lang.Hask.Execution where

import FP

import Lang.Hask.Semantics
import MAAM
import Lang.Hask.CPS

class 
  ( PartialOrder (ς Call)
  , JoinLattice (ς Call)
  , Difference (ς Call)
  , Inject ς'
  , MonadStep ς' m
  , Isomorphism (ς' Call) (ς Call)
  ) => Execution ς ς' m | m -> ς, m -> ς'

exec :: forall ς ς' ν lτ dτ m. (Analysis ν lτ dτ m, Execution ς ς' m) => P m -> Call -> ς Call
exec m = collect (isoto . mstepγP m call . isofrom) . (isoto :: ς' Call -> ς Call) . inj

execDiffs :: forall ς ς' ν lτ dτ m. (Analysis ν lτ dτ m, Execution ς ς' m) => P m -> Call -> [ς Call]
execDiffs m = collectDiffs (isoto . mstepγP m call . isofrom) . (isoto :: ς' Call -> ς Call) . inj
