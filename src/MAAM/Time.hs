module MAAM.Time where

import FP
import qualified FP.Pretty as P
import GHC.TypeLits

class Time ψ τ | τ -> ψ where
  tzero :: τ
  tick :: ψ -> τ -> τ

-- Concrete
newtype Cτ ψ = Cτ [ψ]
  deriving (Eq, Ord, Pretty, Container ψ, Iterable ψ, Buildable ψ)
instance Functorial Eq Cτ where functorial = W
instance Functorial Ord Cτ where functorial = W
instance Functorial Pretty Cτ where functorial = W
instance Bot (Cτ ψ) where bot = nil
instance Time ψ (Cτ ψ) where { tzero = bot ; tick = (&) }

-- kCFA
newtype Kτ (k :: Nat) ψ = Kτ [ψ]
  deriving (Eq, Ord, Pretty, Container ψ, Iterable ψ, Buildable ψ)
instance Functorial Eq (Kτ k) where functorial = W
instance Functorial Ord (Kτ k) where functorial = W
instance Functorial Pretty (Kτ k) where functorial = W
instance Bot (Kτ k ψ) where bot = nil
instance (KnownNat k) => Time ψ (Kτ k ψ) where
  tzero = bot
  tick x y = fromList $ firstN (natVal (P :: P k)) $ toList $ x & y

-- 0CFA
data Zτ ψ = Zτ
  deriving (Eq, Ord)
instance Pretty (Zτ a) where
  pretty Zτ = P.lit "∙"
instance Functorial Eq Zτ where functorial = W
instance Functorial Ord Zτ where functorial = W
instance Functorial Pretty Zτ where functorial = W
instance Bot (Zτ ψ) where bot = Zτ
instance Time ψ (Zτ ψ) where { tzero = bot ; tick = const id }
