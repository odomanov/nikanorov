-- примеры: синтез двух теорий
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module _ where

open import Cubical.Foundations.Function --using (uncurry)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (ℙ; isSetℙ; _∈_)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.FinData using (Fin; zero; suc; one; two; three; four; five; toℕ)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ; max; isEvenT; isPropIsEvenT)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤)
open import Cubical.Data.Sigma using (_×_; _,_; ∃; ∃-syntax)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup; head; tail; foldr; map) 
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.HITs.PropositionalTruncation 

open import Base

open РодСтруктуры

-- первая структура: множество и его булеан
M1 : M-граф 1 _
M1 = 𝔅 zero & base zero & ∅

-- вторая структура: бинарное отношение на двух множествах
M2 : M-граф 2 _
M2 = 𝔅 zero & 𝔇 (zero ∷ one ∷ []) & base zero & base one & ∅

hℕ : hSet _
hℕ = ℕ , isSetℕ

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

-- проверяем их типы
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

-- для упрощения используем PropRel, отличный от библиотечного
PropRel : ∀ {ℓX ℓY} (X : Type ℓX) (Y : Type ℓY) (ℓ : Level) → Type _
PropRel X Y ℓ = X → Y → hProp ℓ

IsUniversal : ∀ {ℓX ℓY ℓ'} {X : Type ℓX} {Y : Type ℓY} → PropRel X Y ℓ' → Type _
IsUniversal R = ∀ x y → fst (R x y)

IsUniversal× : ∀ {ℓX ℓY} {X : Type ℓX} {Y : Type ℓY} → ℙ (X × Y) → hProp _
IsUniversal× R× = (∃[ R ∈ PropRel _ _ _ ] (IsUniversal R) × (R× ≡ uncurry R))
                  , squash₁

-- добавляем ступень
S7 = M-Ступень BS2 (𝔅 zero & M2) zero

-- множество универсальных отношений
universal : S7
universal = IsUniversal×

-- отношения на мн-ве чётных чисел

-- мн-во чётных чисел
s : S1
s x = isEvenT x , isPropIsEvenT x

hs : hSet _ 
hs = ℙΣ s , isSetΣSndProp isSetℕ λ n → snd (s n)

BS3 : BaseSets _
BS3 = hs ∷ hs ∷ []

-- ступени синтезированной структуры
S3' = M-Ступень BS3 M2 zero
S4' = M-Ступень BS3 M2 one
S5' = M-Ступень BS3 M2 two
S6' = M-Ступень BS3 M2 three

-- проверяем их типы
_ : S3' ≡ ℙ (⟨ hs ⟩ × ⟨ hs ⟩)
_ = refl

_ : S3' ≡ ℙ (ℙΣ s × ℙΣ s) 
_ = refl

_ : S4' ≡ ⟨ hs ⟩ × ⟨ hs ⟩
_ = refl

_ : S5' ≡ ⟨ hs ⟩ 
_ = refl

_ : S6' ≡ ⟨ hs ⟩
_ = refl

