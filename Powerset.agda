-- дополнительные операции для Powerset
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

module Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Powerset using (ℙ; _∈_; ∈-isProp; isSetℙ)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Sigma using (_×_; _,_; ∃; ∃!; Σ≡Prop; ∃-syntax)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓX ℓY : Level
    X : Type ℓX
    Y : Type ℓY
  
-- подтип X, соответствующий ℙ X
ℙΣ : ∀ (X : Type ℓX) (P : ℙ X) → Type ℓX
ℙΣ X P = Σ[ x ∈ X ] ⟨ P x ⟩

ℙΣIsSet : ∀ (X : hSet ℓX) (P : ℙ ⟨ X ⟩) → isSet (ℙΣ {ℓX} ⟨ X ⟩ P)
ℙΣIsSet X P = isSetΣSndProp (X .snd) λ x → P x .snd

_∩ᵖ_ : ℙ X → ℙ X → ℙ X
-- A ∩ᵖ B = λ x → (x ∈ A) × (x ∈ B) , isProp× (∈-isProp A x) (∈-isProp B x)
A ∩ᵖ B = λ x → A x ⊓ B x 

_∪ᵖ_ : ℙ X → ℙ X → ℙ X
A ∪ᵖ B = λ x → A x ⊔ B x   -- ∥ (x ∈ A) ⊎ (x ∈ B) ∥₁ , squash₁  

_→ᵖ_ : ℙ X → ℙ X → ℙ X
A →ᵖ B = λ x → (A x .fst → B x .fst) , isProp→ (B x .snd)

¬ᵖ : ℙ X → ℙ X
¬ᵖ A = A →ᵖ λ x → ⊥* , λ ()

_╲ᵖ_ : ℙ X → ℙ X → ℙ X
A ╲ᵖ B = A ∩ᵖ (¬ᵖ B)

_፥ᵖ_ : ℙ X → ℙ X → ℙ X
A ፥ᵖ B = (A ∪ᵖ B) ╲ᵖ (A ∩ᵖ B)

_×ᵖ_ : ℙ X → ℙ Y → ℙ (X × Y)
A ×ᵖ B = λ { (x , y) → (x ∈ A) × (y ∈ B) , isProp× (∈-isProp A x) (∈-isProp B y) }

-- частный случай условия на бинарное отношения
_^ᵖ_ : ∀ {ℓX ℓY} {X : Type ℓX} {Y : Type ℓY} → ℙ Y → ℙ X → ℙ (ℙ (X × Y))
_^ᵖ_ {ℓX} {ℓY} {X} {Y} B A pairs = isfunA→B pairs , squash₁
  where
  isfunA→B : ℙ (X × Y) → Type _  --(ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓY)) 
  isfunA→B ps = ∃[ f ∈ (ℙΣ {ℓX} X A → ℙΣ {ℓY} Y B) ]
                 (ℙΣ (X × Y) ps) ≡ (Σ[ x ∈ ℙΣ X A ] ⟨ (B (fst (f x))) ⟩)
