module MAAM.Classes.AAM where

import FP
import MAAM.Classes.Temporal

class (Temporal (LexicalTemporal μ), Temporal (DynamicTemporal μ)) => AAM μ where
  type LexicalTemporal μ :: *
  type DynamicTemporal μ :: *
  lexical :: μ -> LexicalTemporal μ
  dynamic :: μ -> DynamicTemporal μ

type LexicalTime μ = Time (LexicalTemporal μ)
type DynamicTime μ = Time (DynamicTemporal μ)

lexicalTimeP :: μ -> P ψ -> P (LexicalTime μ ψ)
lexicalTimeP _ P = P

dynamicTimeP :: μ -> P ψ -> P (DynamicTime μ ψ)
dynamicTimeP _ P = P
