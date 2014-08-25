module MAAM.Classes.AAM where

import FP
import MAAM.Classes.Temporal

class (Temporal (LexicalTemporal μ), Temporal (DynamicTemporal μ)) => AAM μ where
  type LexicalTemporal μ :: *
  type DynamicTemporal μ :: *
  lexical :: μ -> LexicalTemporal μ
  dynamic :: μ -> DynamicTemporal μ

newtype LexicalTime μ ψ = LexicalTime { runLexicalTime :: Time (LexicalTemporal μ) ψ }
instance (AAM μ, Eq ψ) => Eq (LexicalTime μ ψ) where
  (==) = 
    with (functorial :: W (Eq (Time (LexicalTemporal μ) ψ))) $
    (==) `on` runLexicalTime
instance (AAM μ, Ord ψ) => Ord (LexicalTime μ ψ) where
  compare = 
    with (functorial :: W (Ord (Time (LexicalTemporal μ) ψ))) $
    compare `on` runLexicalTime
instance (AAM μ, Pretty ψ) => Pretty (LexicalTime μ ψ) where
  pretty = 
    with (functorial :: W (Pretty (Time (LexicalTemporal μ) ψ))) $
    pretty . runLexicalTime

newtype DynamicTime μ ψ = DynamicTime { runDynamicTime :: Time (DynamicTemporal μ) (LexicalTime μ ψ) }
instance (AAM μ, Eq ψ) => Eq (DynamicTime μ ψ) where
  (==) =
    with (functorial :: W (Eq (Time (DynamicTemporal μ) (LexicalTime μ ψ)))) $
    (==) `on` runDynamicTime
instance (AAM μ, Ord ψ) => Ord (DynamicTime μ ψ) where
  compare =
    with (functorial :: W (Ord (Time (DynamicTemporal μ) (LexicalTime μ ψ)))) $
    compare `on` runDynamicTime
instance (AAM μ, Pretty ψ) => Pretty (DynamicTime μ ψ) where
  pretty =
    with (functorial :: W (Pretty (Time (DynamicTemporal μ) (LexicalTime μ ψ)))) $
    pretty . runDynamicTime

lexicalTimeP :: μ -> P ψ -> P (LexicalTime μ ψ)
lexicalTimeP _ P = P
lexicalTimeL :: μ -> P ψ -> Lens (LexicalTime μ ψ) (Time (LexicalTemporal μ) ψ)
lexicalTimeL _ P = isoLens runLexicalTime LexicalTime

dynamicTimeP :: μ -> P ψ -> P (DynamicTime μ ψ)
dynamicTimeP _ P = P
dynamicTimeL :: μ -> P ψ -> Lens (DynamicTime μ ψ) (Time (DynamicTemporal μ) (LexicalTime μ ψ))
dynamicTimeL _ P = isoLens runDynamicTime DynamicTime
