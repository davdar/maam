module MAAM.Instances.Temporal where

import FP
import MAAM.Classes.Temporal
import qualified FP.Pretty as P

-- Concrete {{{

data Cτ = Cτ

instance Temporal Cτ where
  type Time Cτ = []
  tzero P = []
  tick Cτ = (:)

-- }}}

-- Zero (k=0) {{{

data Zτ = Zτ

data Zero a = Zero
  deriving (Eq, Ord)
instance Pretty (Zero a) where
  pretty Zero = P.lit "∙"
instance Functorial Eq Zero where functorial = W
instance Functorial Ord Zero where functorial = W
instance Functorial Pretty Zero where functorial = W

instance Temporal Zτ where
  type Time Zτ = Zero
  tzero P = Zero
  tick Zτ = const id

-- }}}

-- Last-k-sites {{{

data Kτ = Kτ Int

instance Temporal Kτ where
  type Time Kτ = []
  tzero P = []
  tick (Kτ k) = firstN k .: (:)

-- }}}
