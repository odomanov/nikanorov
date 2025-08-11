-- примеры
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

module _ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (ℙ; isSetℙ; _∈_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.FinData using (Fin; zero; suc; one; two; three; four; five; toℕ)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ; max)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤)
open import Cubical.Data.Sigma using (_×_; _,_; ∃; ∃-syntax)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup; head; tail; foldr; map) 
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)

open import Base

hℕ : hSet _
hℕ = ℕ , isSetℕ

hBool : hSet _
hBool = Bool , isSetBool

BS₁ : BaseSets _
BS₁ = hℕ ∷ []

BS₂ : BaseSets _
BS₂ = hℕ ∷ hBool ∷ []

open РодСтруктуры 

_ : Ступень BS₁ (base zero) ≡ ℕ
_ = refl

_ : Ступень BS₁ (base zero) 
_ = 5

_ : Ступень BS₁ (𝔅 (base zero)) ≡ ℙ ℕ
_ = refl

_ : Ступень BS₁ (𝔅 (base zero))
_ = λ n → (n ≤ 7) , isProp≤ 

_ : Ступень BS₂ (𝔇 (base zero ∷ base one ∷ [])) ≡ ℕ × Bool
_ = refl

_ : Ступень BS₂ (𝔇 (base zero ∷ base one ∷ []))
_ = 4 , true

-- кортеж из трёх элементов
_ : Ступень BS₂ (𝔇 (base zero ∷ base one ∷ base zero ∷ [])) ≡ ℕ × Bool × ℕ
_ = refl

_ : Ступень BS₂ (𝔇 (base zero ∷ base one ∷ base zero ∷ []))
_ = 2 , true , 11

_ : Ступень BS₂ (𝔇 (base zero ∷ base one ∷ base one ∷ [])) ≡ ℕ × Bool × Bool
_ = refl

_ : Ступень BS₂ (𝔇 (base zero ∷ base one ∷ base one ∷ []))
_ = 7 , false , true

_ : Ступень BS₂ (𝔅 (𝔇 (base zero ∷ base one ∷ []))) ≡ ℙ (ℕ × Bool)
_ = refl

_ : Ступень BS₂ (𝔅 (𝔇 (base zero ∷ base one ∷ [])))
_ = λ { (n , b) → (n ≤ 7) , isProp≤ } 

_ : Ступень BS₂ (𝔅 (𝔇 (base zero ∷ base one ∷ base one ∷ [])))
_ = λ { (n , _ , _) → (n ≤ 7) , isProp≤ } 

_ : Ступень BS₂ (𝔅 (𝔇 (base zero ∷ base one ∷ base one ∷ []))) ≡ ℙ (ℕ × Bool × Bool)
_ = refl

_ : Ступень BS₂ (𝔅 (𝔇 (base zero ∷ base one ∷ base one ∷ [])))
_ = λ x → ((fst x) ≡ 7) , isSetℕ _ _  


