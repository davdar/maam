open import Data.String
open import Data.Maybe hiding (map)
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (<_,_>; _,_)

Name : Set
Name = String

mutual
  data Atom : Set where
    var : Name → Atom
    ⟨λ⟩_⇒_ : Name → Exp → Atom

  data Exp : Set where
    atom : Atom → Exp
    _∙_ : Exp → Exp → Exp

mutual
    data Val : Set where
      ⟨λ⟩_⇒_,_ : Name → Exp → Env → Val

    Env : Set
    Env = Name → Maybe Val 

data Frame : Set where
  □∙_ : Exp → Frame
  _∙□ : Maybe Val → Frame

data C₁ : Set where
  <_,_> : Exp → Env → C₁

data LFrame : Set where
  _^_ : Frame → C₁ → LFrame

Kon : Set
Kon = List LFrame

data CacheResult : Set where
  cached : Maybe Val → CacheResult
  seen : CacheResult
  unseen : CacheResult

Cache : Set
Cache = C₁ → CacheResult

data C₂ : Set where
  <_,_,_> : Exp → Env → Kon → C₂

[_↦_] : Name → Maybe Val → Env → Env
[ x ↦ v ] ρ y with x ≟ y
... | yes _ = v
... | no _ = ρ y

[[_↦_]] : C₁ → CacheResult → Cache → Cache
[[_↦_]] = whatever
  where
    postulate whatever : _

A[_] : Env → Atom → Maybe Val
A[ ρ ] (var x) = ρ x
A[ ρ ] (⟨λ⟩ x ⇒ e) = just (⟨λ⟩ x ⇒ e , ρ)

-- non-caching semantics
data _⟶₂_ : C₂ → C₂ → Set where
  e₁-ret  : ∀ {a ρ e ℓ κ}      → < atom a  , ρ , □∙ e                     ^ ℓ ∷ κ > ⟶₂ < e  , ρ                   , A[ ρ ] a ∙□ ^ < e , ρ >  ∷ κ >
  e₂-ret  : ∀ {a ρ x e ρ' ℓ κ} → < atom a  , ρ , just (⟨λ⟩ x ⇒ e , ρ') ∙□ ^ ℓ ∷ κ > ⟶₂ < e  , [ x ↦ A[ ρ ] a ] ρ' ,                            κ >
  e₁-push : ∀ {e₁ e₂ ρ κ}      → < e₁ ∙ e₂ , ρ ,                                κ > ⟶₂ < e₁ , ρ                   , □∙ e₂       ^ < e₁ , ρ > ∷ κ >

data C₃ : Set where
  <_,_,_,_> : Exp → Env → Kon → Cache → C₃

data _⟶₃_ : C₃ → C₃ → Set where
  $ed-e₁     : ∀ {e₁ e₂ ℓ ρ v κ $}      → $ < e₁ , ρ > ≡ cached v → < e₁ , ρ , □∙ e₂ ^ ℓ                     ∷ κ , $ > ⟶₃ < e₂ , ρ            , v ∙□ ^ < e₂ , ρ > ∷ κ , $ >
  $ed-e₂     : ∀ {e₁ e₂ ℓ x ρ ρ' v κ $} → $ < e₁ , ρ > ≡ cached v → < e₁ , ρ , just (⟨λ⟩ x ⇒ e₂ , ρ') ∙□ ^ ℓ ∷ κ , $ > ⟶₃ < e₂ , [ x ↦ v ] ρ' ,                     κ , $ >

  $ed-unseen : ∀ {e e' ρ ρ' κ κ' $}     → $ < e , ρ > ≡ unseen
                                        → < e , ρ , κ > ⟶₂ < e' , ρ' , κ' >
                                        → < e , ρ , κ , $ > ⟶₃ < e' , ρ' , κ' , [[ < e , ρ > ↦ seen ]] $ >
  -- things to do 
  -- ∙ we should separate cached rules to only deal with (e₁ ∙ e₂) expressions (ruling out atom expression).
  -- ∙ we need to implement $ (ideally using a map or assoc list, and with type classes for the update function using decidable equality on the domain).
  -- ∙ the actual proofs (⟶₃ is a simulation of ⟶₂, under some conditions about the $)


_⟶₂*_ : C₂ → C₂ → Set
_⟶₂*_ = whatever
  where
    postulate whatever : _

_⟶₃*_ : C₃ → C₃ → Set
_⟶₃*_ = whatever
  where
    postulate whatever : _

cache-wf : Cache → Set
cache-wf $ = ∀ e ρ v → $ < e , ρ > ≡ cached v → Σ[ a ∈ Atom ] Σ[ ρ' ∈ Env ] (∀ κ → < e , ρ , κ > ⟶₂* < atom a , ρ' , κ > × A[ ρ ] a ≡ v)

-- what we don't get is a simulation for looping behavior.  but this is WANTED behavior.
the-theorem : Set
the-theorem = ∀ {e a ρ ρ' κ $}
  → cache-wf $
  → < e , ρ , κ > ⟶₂* < atom a , ρ' , κ >
  → Σ[ $' ∈ Cache ] < e , ρ , κ , $ > ⟶₃* < atom a , ρ' , κ , $' > × cache-wf $'

-- this theorem is trivial, and only is about a single step (not *)
smaller-theorem : Set
smaller-theorem = ∀ {a e ρ ρ' κ κ' $} 
  → cache-wf $
  → < atom a , ρ , κ > ⟶₂ < e , ρ' , κ' >
  → Σ[ $' ∈ Cache ] < atom a , ρ , κ , $ > ⟶₃ < e , ρ' , κ' , $' > × cache-wf $'
