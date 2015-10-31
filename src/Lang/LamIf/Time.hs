module Lang.LamIf.Time where

import FP

data TimeParam = TimeParam
  { lexicalCallDepth ∷ Maybe ℕ
  , dynamicCallDepth ∷ Maybe ℕ
  , lexicalObjDepth ∷ Maybe ℕ
  , dynamicObjDepth ∷ Maybe ℕ
  }
makeLenses ''TimeParam

icfa ∷ TimeParam
icfa = TimeParam Nothing Nothing Nothing Nothing

zcfa ∷ TimeParam
zcfa = TimeParam (Just (𝕟 0)) (Just (𝕟 0)) (Just (𝕟 0)) (Just (𝕟 0))

lkcfa ∷ ℕ → TimeParam
lkcfa n = zcfa { lexicalCallDepth = Just n }

kcfa ∷ ℕ → TimeParam
kcfa n = zcfa { dynamicCallDepth = Just n }

locfa ∷ ℕ → TimeParam
locfa n = zcfa { lexicalObjDepth = Just n }

ocfa ∷ ℕ → TimeParam
ocfa n = zcfa { dynamicObjDepth = Just n }
