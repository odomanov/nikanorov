-- примеры: бинарные отношения + порождение мн-ва бинарных отношений
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module _ where

open import Cubical.Foundations.Powerset using (ℙ; isSetℙ; _∈_)
open import Cubical.Foundations.Function --using (uncurry)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.FinData using (Fin; zero; suc; one; two; three; four; five; toℕ)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ; max)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤)
open import Cubical.Data.Sigma --using (_×_; _,_; ∃; ∃-syntax;)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup; head; tail; foldr; map) 
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.HITs.PropositionalTruncation 

open import Base

open РодСтруктуры

hℕ : hSet _
hℕ = ℕ , isSetℕ

-- первая структура: множество и его булеан
M1 : M-граф 1 _
M1 = 𝔅 zero & base zero & ∅

-- вторая структура: бинарное отношение на двух множествах
M2 : M-граф 2 _
M2 = 𝔅 zero & 𝔇 (zero ∷ one ∷ []) & base zero & base one & ∅

BS1 : BaseSets _
BS1 = hℕ ∷ []

S1 = M-Ступень BS1 M1 zero
S2 = M-Ступень BS1 M1 one

_ : S1 ≡ ℙ ℕ
_ = refl

_ : S2 ≡ ℕ
_ = refl

hS1 : hSet _
hS1 = S1 , СтупеньIsSet BS1 (M-Схема M1 zero)

hS2 : hSet _
hS2 = S2 , isSetℕ

-- ступени первой структуры как базисные множества второй
BS2 : BaseSets _
BS2 = hS1 ∷ hS2 ∷ []

-- ступени синтезированной структуры
S3 = M-Ступень BS2 M2 zero
S4 = M-Ступень BS2 M2 one
S5 = M-Ступень BS2 M2 two
S6 = M-Ступень BS2 M2 three

_ : S3 ≡ ℙ (ℙ ℕ × ℕ)
_ = refl

_ : S4 ≡ ℙ ℕ × ℕ
_ = refl

_ : S5 ≡ ℙ ℕ
_ = refl

_ : S6 ≡ ℕ
_ = refl

-- теория универсального отношения в синтезированной структуре
open import Cubical.Relation.Binary.Base using (Rel)

-- обобщение PropRel на типы разных универсумов
PropRel : ∀ {ℓX ℓY} (X : Type ℓX) (Y : Type ℓY) (ℓ' : Level)
        → Type (ℓ-max (ℓ-max ℓX ℓY) (ℓ-suc ℓ'))
PropRel X Y ℓ' = Σ[ R ∈ Rel X Y ℓ' ] ∀ a b → isProp (R a b)

IsUniversal : ∀ {ℓX ℓY ℓ'} {X : Type ℓX} {Y : Type ℓY} (R : PropRel X Y ℓ') → Type _
IsUniversal {X = X} {Y = Y} R = (x : X) (y : Y) → R .fst x y

to× : ∀ {ℓX ℓY ℓ} {X : Type ℓX} {Y : Type ℓY} (R : PropRel X Y ℓ) → X × Y → hProp ℓ
to× R x = uncurry (λ a b → R .fst a b , R .snd a b) x

IsUniversal× : ∀ {ℓX ℓY} {X : Type ℓX} {Y : Type ℓY} (R× : ℙ (X × Y)) → hProp _
IsUniversal× {X = X} {Y = Y} R× =
  (∃[ R ∈ PropRel X Y _ ] (IsUniversal R) × (R× ≡ to× R)) , squash₁

-- добавляем ступень
S7 = M-Ступень BS2 (𝔅 zero & M2) zero

-- множество универсальных отношений
universal : S7
universal = IsUniversal×
