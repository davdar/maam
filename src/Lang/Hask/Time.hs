module Lang.Hask.Time where

import FP
import GHC.TypeLits
import qualified FP.Pretty as P

class Time ψ τ | τ -> ψ where
  tzero :: τ
  tick :: ψ -> τ -> τ

-- Concrete
newtype Cτ ψ = Cτ [ψ]
  deriving (Eq, Ord, Pretty, Container ψ, Iterable ψ, Buildable ψ)
instance Bot (Cτ ψ) where bot = nil
instance Time ψ (Cτ ψ) where { tzero = bot ; tick = (&) }
cτ :: P Cτ
cτ = P

-- kCFA
newtype Kτ (k :: Nat) ψ = Kτ [ψ]
  deriving (Eq, Ord, Pretty, Container ψ, Iterable ψ, Buildable ψ)
instance Bot (Kτ k ψ) where bot = nil
instance (KnownNat k) => Time ψ (Kτ k ψ) where
  tzero = bot
  tick x y = fromList $ firstN (natVal (P :: P k)) $ toList $ x & y
kτ :: P (Kτ 1)
kτ = P

-- 0CFA
data Zτ ψ = Zτ
  deriving (Eq, Ord)
instance Pretty (Zτ a) where
  pretty Zτ = P.lit "∙"
instance Bot (Zτ ψ) where bot = Zτ
instance Time ψ (Zτ ψ) where { tzero = bot ; tick = const id }
zτ :: P Zτ
zτ = P
