module MAAM.Instances.Temporal where

import FP
import MAAM.Classes.Temporal
import qualified FP.Pretty as P
import GHC.TypeLits

-- Concrete
newtype Cτ ψ = Cτ [ψ]
  deriving (Eq, Ord, Pretty)
deriving instance Iterable ψ (Cτ ψ)
deriving instance ListLike ψ (Cτ ψ)
instance Functorial Eq Cτ where functorial = W
instance Functorial Ord Cτ where functorial = W
instance Functorial Pretty Cτ where functorial = W
instance Temporal Cτ where
  tzero = nil
  tick = cons

-- kCFA
newtype Kτ (k :: Nat) ψ = Kτ [ψ]
  deriving (Eq, Ord, Pretty, Iterable ψ, ListLike ψ)
instance Functorial Eq (Kτ k) where functorial = W
instance Functorial Ord (Kτ k) where functorial = W
instance Functorial Pretty (Kτ k) where functorial = W
instance (KnownNat k) => Temporal (Kτ k) where
  tzero = nil
  tick x y = toListLike $ firstN (natVal (P :: P k)) $ fromListLike $ cons x y

-- 0CFA
data Zτ ψ = Zτ
  deriving (Eq, Ord)
instance Pretty (Zτ a) where
  pretty Zτ = P.lit "∙"
instance Functorial Eq Zτ where functorial = W
instance Functorial Ord Zτ where functorial = W
instance Functorial Pretty Zτ where functorial = W
instance Temporal Zτ where
  tzero = Zτ
  tick = const id
