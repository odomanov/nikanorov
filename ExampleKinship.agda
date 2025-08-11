-- пример: родственные отношения
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

module _ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; uncurry)
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

open РодСтруктуры 
  
data Human : Type where
  h1 h2 h3 h4 h5 h6 : Human
  isset : isSet Human

-- отношение родитель-ребёнок
data R : Human → Human → Type where  
  r12 : R h1 h2
  r13 : R h1 h3
  r24 : R h2 h4
  r25 : R h2 h4
  r36 : R h3 h6

BS : BaseSets _
BS = (Human , Human.isset) ∷ []

LS : Vec (СхемаСтупени 1) 2
LS = base zero ∷ base zero ∷ []

P : Ступень BS (𝔅 (𝔇 LS))
P = λ x → ∥ uncurry R x ∥₁ , isPropPropTrunc

-- Родители : Ступень BS (𝔅 (base zero))      -- ?
Родители : ℙ (Lift (Ступень BS (base zero)))
Родители = Pr BS {LS = LS} P zero

-- Дети : Ступень BS (𝔅 (base zero))          -- ?
Дети = Pr BS {LS = LS} P one


_ : lift h1 ∈ Родители
_ = ∣ (h1 , h2) , ∣ r12 ∣₁ , refl ∣₁

_ : lift h4 ∈ Дети
_ = ∣ (h2 , h4) , ∣ r24 ∣₁ , refl ∣₁
  
