module MAAM.Classes.AAM where

import FP

class Time τ where
  tzero :: τ ψ
  tick :: ψ -> τ ψ -> τ ψ

class (Time (LexicalTime μ), Time (DynamicTime μ)) => AAM μ where
  type LexicalTime μ :: * -> *
  type DynamicTime μ :: * -> *

lexicalTimeP :: P μ -> P ψ -> P (LexicalTime μ ψ)
lexicalTimeP P P = P

dynamicTimeP :: P μ -> P ψ -> P (DynamicTime μ ψ)
dynamicTimeP P P = P
