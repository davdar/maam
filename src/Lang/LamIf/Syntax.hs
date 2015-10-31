module Lang.LamIf.Syntax where

import FP

data PreAtom n e = 
    AInteger ℤ 
  | AVar n 
  | ALam n e
makePrisms ''PreAtom
makePrettySum ''PreAtom

mapAtomM ∷ (Monad m) ⇒ (n → m n') → (n → m n') → (e → m e') → PreAtom n e → m (PreAtom n' e')
mapAtomM fVar fBdr fExp = \case
  AInteger i → return $ AInteger i
  AVar n → return AVar <⋅> fVar n
  ALam n e → return ALam <⋅> fBdr n <⋅> fExp e

instance FunctorM (PreAtom n) where mapM f = mapAtomM return return f
instance Functor (PreAtom n) where map f = runID ∘ mapM (ID ∘ f)

data Op = Plus | Minus
  deriving (Eq,Ord)
makePrettySum ''Op

data PreExp n e =
    EAtom (PreAtom n e)
  | EIf e e e
  | ELet n e e
  | EOp Op e e
  | EApp e e
makePrettySum ''PreExp
instance (Pretty n) ⇒ Functorial Pretty (PreExp n) where functorial = W

mapExpM ∷ (Monad m) ⇒ (n → m n') → (n → m n') → (e → m e') → PreExp n e → m (PreExp n' e')
mapExpM fVar fBdr fExp = \case
  EAtom a → return EAtom <⋅> mapAtomM fVar fBdr fExp a
  EIf e₁ e₂ e₃ → return EIf <⋅> fExp e₁ <⋅> fExp e₂ <⋅> fExp e₃
  ELet x e₁ e₂ → return ELet <⋅> fBdr x <⋅> fExp e₁ <⋅> fExp e₂
  EOp o e₁ e₂ → return (EOp o) <⋅> fExp e₁ <⋅> fExp e₂
  EApp e₁ e₂ → return EApp <⋅> fExp e₁ <⋅> fExp e₂

mapExp ∷ (n → n') → (n → n') → (e → e') → PreExp n e → PreExp n' e'
mapExp fVar fBdr fExp = runID ∘ mapExpM (ID ∘ fVar) (ID ∘ fBdr) (ID ∘ fExp)

instance FunctorM (PreExp n) where mapM f = mapExpM return return f
instance Functor (PreExp n) where map f = mapExp id id f

