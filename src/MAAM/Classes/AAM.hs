module MAAM.Classes.AAM where

import FP
import MAAM.Classes.Temporal

class (Temporal (LexicalTemporal μ), Temporal (DynamicTemporal μ)) => AAM μ where
  type LexicalTemporal μ :: *
  type DynamicTemporal μ :: *
  lexical :: μ -> LexicalTemporal μ
  dynamic :: μ -> DynamicTemporal μ

newtype LexicalTime μ ψ = LexicalTime { runLexicalTime :: Time (LexicalTemporal μ) ψ }
deriving instance (Eq (Time (LexicalTemporal μ) ψ)) => Eq (LexicalTime μ ψ)
deriving instance (Ord (Time (LexicalTemporal μ) ψ)) => Ord (LexicalTime μ ψ)
deriving instance (Pretty (Time (LexicalTemporal μ) ψ)) => Pretty (LexicalTime μ ψ)
newtype DynamicTime μ ψ = DynamicTime { runDynamicTime :: Time (DynamicTemporal μ) ψ }
deriving instance (Eq (Time (DynamicTemporal μ) ψ)) => Eq (DynamicTime μ ψ)
deriving instance (Ord (Time (DynamicTemporal μ) ψ)) => Ord (DynamicTime μ ψ)
deriving instance (Pretty (Time (DynamicTemporal μ) ψ)) => Pretty (DynamicTime μ ψ)

lexicalTimeP :: μ -> P ψ -> P (LexicalTime μ ψ)
lexicalTimeP _ P = P
lexicalTimeL :: μ -> P ψ -> Lens (LexicalTime μ ψ) (Time (LexicalTemporal μ) ψ)
lexicalTimeL _ P = isoLens runLexicalTime LexicalTime

dynamicTimeP :: μ -> P ψ -> P (DynamicTime μ ψ)
dynamicTimeP _ P = P
dynamicTimeL :: μ -> P ψ -> Lens (DynamicTime μ ψ) (Time (DynamicTemporal μ) ψ)
dynamicTimeL _ P = isoLens runDynamicTime DynamicTime
