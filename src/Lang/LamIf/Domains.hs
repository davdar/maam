module Lang.LamIf.Domains where

import FP
import Lang.LamIf.Values
import Lang.LamIf.Syntax

data ConcreteVal = 
    CInt ℤ 
  | CClo Closure 
  | CFrame (Frame,Maybe ExpAddr)
  | CBot
  deriving (Eq,Ord)
makePrisms ''ConcreteVal
makePrettySum ''ConcreteVal

instance Val ConcreteVal 
  where
    intI = CInt
    isZeroE = elimMaybe bot (single ∘ (≟) 0) ∘ view cIntL
    delZero (CInt 0) = CBot
    delZero v = v
    cloI = CClo
    cloE = elimMaybe bot single ∘ view cCloL
    frameI = CFrame
    frameE = elimMaybe bot single ∘ view cFrameL
    δ o v₁ v₂ = elimMaybe CBot CInt $ do
      i₁ ← view cIntL v₁
      i₂ ← view cIntL v₂
      return $ case o of
        Plus → i₁ + i₂
        Minus → i₁ - i₂

data AbstractVal = 
    AInt ℤ
  | APos
  | AZero
  | ANeg
  | ANotZero
  | AAnyInt
  | AClo Closure
  | AFrame (Frame,Maybe ExpAddr)
  | ABot
  deriving (Eq, Ord)
makePrisms ''AbstractVal
makePrettySum ''AbstractVal

negateAbstractVal ∷ AbstractVal → AbstractVal
negateAbstractVal (AInt i) = AInt (negate i)
negateAbstractVal APos = ANeg
negateAbstractVal AZero = AZero
negateAbstractVal ANeg = APos
negateAbstractVal AAnyInt = AAnyInt
negateAbstractVal v = v

instance Val AbstractVal
  where
    intI = AInt
    isZeroE (AInt i) = single $ i ≟ 0
    isZeroE APos = single False
    isZeroE AZero = single True
    isZeroE ANeg = single False
    isZeroE AAnyInt = set [True,False]
    isZeroE _ = bot
    delZero (AInt 0) = ABot
    delZero AZero = ABot
    delZero AAnyInt = ANotZero
    delZero v = v
    cloI = AClo
    cloE = elimMaybe bot single ∘ view aCloL
    frameI = AFrame
    frameE = elimMaybe bot single ∘ view aFrameL
    -- TODO: handle NotZero
    δ Plus (AInt i₁) (AInt i₂) = case (i₁ + i₂) ⋚ 0 of
      LT → ANeg
      EQ → AZero
      GT → APos
    δ Plus (AInt i) APos = case i ⋚ 0 of
      LT → AAnyInt
      EQ → APos
      GT → APos
    δ Plus (AInt i) AZero = AInt i
    δ Plus (AInt i) ANeg = case i ⋚ 0 of
      LT → ANeg
      EQ → ANeg
      GT → AAnyInt
    δ Plus (AInt i) ANotZero = case i ⋚ 0 of
      LT → AAnyInt
      EQ → ANotZero
      GT → AAnyInt
    δ Plus (AInt _) AAnyInt = AAnyInt
    δ Plus APos APos = APos
    δ Plus APos AZero = APos
    δ Plus APos ANeg = AAnyInt
    δ Plus APos ANotZero = AAnyInt
    δ Plus APos AAnyInt = AAnyInt
    δ Plus AZero AZero = AZero
    δ Plus AZero ANeg = ANeg
    δ Plus AZero ANotZero = ANotZero
    δ Plus AZero AAnyInt = AAnyInt
    δ Plus ANeg ANeg = ANeg
    δ Plus ANeg ANotZero = AAnyInt
    δ Plus ANeg AAnyInt = AAnyInt
    δ Plus APos (AInt i) = δ Plus (AInt i) APos
    δ Plus AZero (AInt i) = δ Plus (AInt i) AZero
    δ Plus ANeg (AInt i) = δ Plus (AInt i) ANeg
    δ Plus ANotZero (AInt i) = δ Plus (AInt i) ANotZero
    δ Plus AAnyInt (AInt i) = δ Plus (AInt i) AAnyInt
    δ Plus AZero APos = δ Plus APos AZero
    δ Plus ANeg APos = δ Plus APos ANeg
    δ Plus ANotZero APos = δ Plus APos ANotZero
    δ Plus AAnyInt APos = δ Plus APos AAnyInt
    δ Plus ANeg AZero = δ Plus AZero ANeg
    δ Plus ANotZero AZero = δ Plus AZero ANotZero
    δ Plus AAnyInt AZero = δ Plus AZero AAnyInt
    δ Plus ANotZero ANeg = δ Plus ANeg ANotZero
    δ Plus AAnyInt ANeg = δ Plus ANeg AAnyInt
    δ Minus i₁ i₂ = δ Plus i₁ (negateAbstractVal i₂)
    δ _ _ _ = ABot

instance (Ord val,Val val) ⇒ Val (𝒫 val) where
  intI = single ∘ intI
  isZeroE = extendSet isZeroE
  delZero = mapSet delZero
  cloI = single ∘ cloI
  cloE = extendSet cloE
  frameI = single ∘ frameI
  frameE = extendSet frameE
  δ o vM₁ vM₂ = 
    vM₁ ≫=* \ v₁ →
    vM₂ ≫=* \ v₂ →
    single $ δ o v₁ v₂

data DomainParam where
  DomainParam ∷ ∀ val. P val → W (Ord val,POrd val,JoinLattice val,Val val,Difference val,Pretty val) → DomainParam

concrete ∷ DomainParam
concrete = DomainParam (P ∷ P (𝒫 ConcreteVal)) W

abstract ∷ DomainParam
abstract = DomainParam (P ∷ P (𝒫 AbstractVal)) W
