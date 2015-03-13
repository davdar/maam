module Execution where

import Lang.Hask.Semantics
import MAAM

class (Analysis ν lτ dτ m, MonadStep ς m) => Execution ς ν lτ dτ m | m -> ς, m -> ν, m -> lτ, m -> dτ
