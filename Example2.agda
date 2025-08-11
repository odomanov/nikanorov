-- примеры: большая проекция
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

module _ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (ℙ; isSetℙ; _∈_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.FinData using (Fin; zero; suc; one; two; three; four; five; toℕ)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ; max)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤)
open import Cubical.Data.Sigma using (_×_; _,_; ∃; ∃-syntax)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup; head; tail; foldr; map) 
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.HITs.PropositionalTruncation hiding (map) --using (∥_∥₁; ∣_∣₁; squash₁; isPropPropTrunc)

open import Base

hℕ : hSet _
hℕ = ℕ , isSetℕ

hBool : hSet _
hBool = Bool , isSetBool

open РодСтруктуры 

BS : BaseSets _
BS = hℕ ∷ hBool ∷ []

LS : Vec (СхемаСтупени 2) _
LS = base zero ∷ base one ∷ []

S1 = Ступень BS (𝔇 LS)

P1 : ℙ S1
P1 (7 , _) = Unit , isPropUnit
P1 (_ , _) = ⊥* , isProp⊥*

P2 : ℙ ℕ
P2 7 = Unit , isPropUnit
P2 _ = ⊥* , (λ ())

_ : Pr BS {LS = LS} P1 zero ≡ λ n → ∥ Σ (ℕ × Bool) (λ y → (P1 y .fst) × (lower n ≡ fst y)) ∥₁
                                           , isPropPropTrunc  
_ = refl

Pr1 = Pr BS {LS = LS} P1 zero

_ : Pr1 ≡ λ n → ∥ Σ (ℕ × Bool) (λ y → (P1 y .fst) × (lower n ≡ y .fst)) ∥₁
                , isPropPropTrunc  
_ = refl

_ : lift 7 ∈ Pr1
_ = ∣ ((7 , true) , (tt , refl)) ∣₁

-- _ : 8 ∈ Pr1 → ⊥
-- _ = {!!}


_ : Pr BS {LS = LS} P1 one ≡ λ n →
    ∥ Σ (Σ ℕ (λ _ → Bool)) (λ y → Σ (P1 y .fst) (λ _ → lower n ≡ y .snd)) ∥₁
    , isPropPropTrunc  
_ = refl

