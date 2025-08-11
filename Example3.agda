-- примеры: M-граф
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

M1 : M-граф 5 1
M1 = base four & ∅

M2 : M-граф 5 2
M2 = 𝔅 zero &
     base four &
     ∅

M3 : M-граф 5 3
M3 = base four
   & 𝔅 zero
   & base three
   & ∅

M4 : M-граф 5 4
M4 = 𝔅 zero & M3

M5 : M-граф 5 4
M5 = 𝔅 two & M3

M6 : M-граф 5 4
M6 = 𝔅 two 
   & base four
   & 𝔅 zero
   & base three
   & ∅

_ : M5 ≡ M6
_ = refl

M7 : M-граф 5 5
M7 = 𝔇 (one ∷ one ∷ []) & M5
  
