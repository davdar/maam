module MAAM.Classes.AAM where

-- import FP
-- import MAAM.Classes.Temporal
-- import qualified FP.Pretty as P

data Moment τ ψ = Moment
  { momentLoc :: ψ
  , momentTime :: τ ψ
  }

-- class (Temporal (LexicalTime μ), Temporal (DynamicTime μ)) => AAM μ where
--   type LexicalTime μ :: * -> *
--   type DynamicTime μ :: * -> *

-- newtype LexicalTime μ ψ = LexicalTime { runLexicalTime :: Time (LexicalTemporal μ) ψ }
-- instance (AAM μ, Eq ψ) => Eq (LexicalTime μ ψ) where
--   (==) = 
--     with (functorial :: W (Eq (Time (LexicalTemporal μ) ψ))) $
--     (==) `on` runLexicalTime
-- instance (AAM μ, Ord ψ) => Ord (LexicalTime μ ψ) where
--   compare = 
--     with (functorial :: W (Ord (Time (LexicalTemporal μ) ψ))) $
--     compare `on` runLexicalTime
-- instance (AAM μ, Pretty ψ) => Pretty (LexicalTime μ ψ) where
--   pretty = 
--     with (functorial :: W (Pretty (Time (LexicalTemporal μ) ψ))) $
--     pretty . runLexicalTime

-- data DynamicMoment μ ψ = DynamicMoment
--   { dynamicLoc :: ψ
--   , dynamicLexicalTime :: LexicalTime μ ψ
--   }
--   deriving (Eq, Ord)
-- instance (AAM μ, Pretty ψ) => Pretty (DynamicMoment μ ψ) where
--   pretty (DynamicMoment l lτ) = P.collection "<" ">" "," 
--     [ exec [P.pun "𝓁=", pretty l]
--     , exec [P.pun "lτ=", pretty lτ]
--     ]
-- newtype DynamicTime μ ψ = DynamicTime 
--   { runDynamicTime :: Time (DynamicTemporal μ) (DynamicMoment μ ψ) }
-- instance (AAM μ, Eq ψ) => Eq (DynamicTime μ ψ) where
--   (==) =
--     with (bifunctorial :: W (Eq (ψ, LexicalTime μ ψ))) $
--     with (functorial :: W (Eq (Time (DynamicTemporal μ) (DynamicMoment μ ψ)))) $
--     (==) `on` runDynamicTime
-- instance (AAM μ, Ord ψ) => Ord (DynamicTime μ ψ) where
--   compare =
--     with (bifunctorial :: W (Ord (ψ, LexicalTime μ ψ))) $
--     with (functorial :: W (Ord (Time (DynamicTemporal μ) (DynamicMoment μ ψ)))) $
--     compare `on` runDynamicTime
-- instance (AAM μ, Pretty ψ) => Pretty (DynamicTime μ ψ) where
--   pretty =
--     with (functorial :: W (Pretty (Time (DynamicTemporal μ) (DynamicMoment μ ψ)))) $
--     pretty . runDynamicTime
-- 
-- lexicalTimeP :: μ -> P ψ -> P (LexicalTime μ ψ)
-- lexicalTimeP _ P = P
-- lexicalTimeL :: μ -> P ψ -> Lens (LexicalTime μ ψ) (Time (LexicalTemporal μ) ψ)
-- lexicalTimeL _ P = isoLens runLexicalTime LexicalTime
-- 
-- dynamicTimeP :: μ -> P ψ -> P (DynamicTime μ ψ)
-- dynamicTimeP _ P = P
-- dynamicTimeL :: μ -> P ψ -> Lens (DynamicTime μ ψ) (Time (DynamicTemporal μ) (DynamicMoment μ ψ))
-- dynamicTimeL _ P = isoLens runDynamicTime DynamicTime
