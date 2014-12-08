module MAAM.Time where

import FP
import qualified FP.Pretty as P
import MAAM.Initial
import GHC.TypeLits

class Time τ where
  tzero :: τ ψ
  tick :: ψ -> τ ψ -> τ ψ

-- Concrete
newtype Cτ ψ = Cτ [ψ]
  deriving (Eq, Ord, Pretty, Iterable ψ, Buildable ψ, ListLike ψ)
instance Functorial Eq Cτ where functorial = W
instance Functorial Ord Cτ where functorial = W
instance Functorial Pretty Cτ where functorial = W
instance Initial (Cτ ψ) where initial = nil
instance Time Cτ where
  tzero = initial
  tick = cons

-- kCFA
newtype Kτ (k :: Nat) ψ = Kτ [ψ]
  deriving (Eq, Ord, Pretty, Iterable ψ, Buildable ψ, ListLike ψ)
instance Functorial Eq (Kτ k) where functorial = W
instance Functorial Ord (Kτ k) where functorial = W
instance Functorial Pretty (Kτ k) where functorial = W
instance Initial (Kτ k ψ) where initial = nil
instance (KnownNat k) => Time (Kτ k) where
  tzero = initial
  tick x y = toListLike $ firstN (natVal (P :: P k)) $ fromListLike $ cons x y

-- 0CFA
data Zτ ψ = Zτ
  deriving (Eq, Ord)
instance Pretty (Zτ a) where
  pretty Zτ = P.lit "∙"
instance Functorial Eq Zτ where functorial = W
instance Functorial Ord Zτ where functorial = W
instance Functorial Pretty Zτ where functorial = W
instance Initial (Zτ ψ) where initial = Zτ
instance Time Zτ where
  tzero = initial
  tick = const id
