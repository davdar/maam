module MAAM.Time where

import FP
import qualified FP.Pretty as P
import GHC.TypeLits

class Time τ where
  tzero :: τ ψ
  tick :: ψ -> τ ψ -> τ ψ

-- Concrete
newtype Cτ ψ = Cτ [ψ]
  deriving (Eq, Ord, Pretty, Container ψ, Iterable ψ, Buildable ψ)
instance Functorial Eq Cτ where functorial = W
instance Functorial Ord Cτ where functorial = W
instance Functorial Pretty Cτ where functorial = W
instance Bot (Cτ ψ) where bot = nil
instance Time Cτ where { tzero = bot ; tick = (&) }

-- kCFA
newtype Kτ (k :: Nat) ψ = Kτ [ψ]
  deriving (Eq, Ord, Pretty, Container ψ, Iterable ψ, Buildable ψ)
instance Functorial Eq (Kτ k) where functorial = W
instance Functorial Ord (Kτ k) where functorial = W
instance Functorial Pretty (Kτ k) where functorial = W
instance Bot (Kτ k ψ) where bot = nil
instance (KnownNat k) => Time (Kτ k) where
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
instance Time Zτ where { tzero = bot ; tick = const id }
