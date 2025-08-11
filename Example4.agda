-- примеры: графы и ступени
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

module _ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (ℙ; isSetℙ; _∈_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.FinData using (Fin; zero; suc; one; two; three; four; five; toℕ)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ; max)
open import Cubical.Data.Sigma using (_×_; _,_; ∃; ∃-syntax)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup; head; tail; foldr; map) 

open import Base

hℕ : hSet _
hℕ = ℕ , isSetℕ

hBool : hSet _
hBool = Bool , isSetBool

BS : BaseSets _
BS = hℕ ∷ hBool ∷ []

open РодСтруктуры BS

M1 : M-граф 2 _
M1 = base zero & ∅

_ : M-Ступень M1 zero ≡ ℕ
_ = refl

M2 : M-граф 2 _
M2 = 𝔅 zero & M1

_ : M-Ступень M2 zero ≡ ℙ ℕ
_ = refl

_ : M-Ступень M2 one ≡ ℕ
_ = refl

M3 : M-граф 2 _
M3 = 𝔇 (zero ∷ one ∷ []) & base one & M2

_ : M-Ступень M3 zero ≡ Bool × (ℙ ℕ)
_ = refl

_ : M-Ступень M3 one ≡ Bool
_ = refl

_ : M-Ступень M3 two ≡ ℙ ℕ
_ = refl

_ : M-Ступень M3 three ≡ ℕ
_ = refl

M4 : M-граф 2 _
M4 = 𝔅 zero & M3

_ : M-Ступень M4 zero ≡ ℙ (Bool × (ℙ ℕ))
_ = refl
  
