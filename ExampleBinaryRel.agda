-- примеры: бинарные отношения + порождение мн-ва бинарных отношений
-- TODO: добавить функцию как бинарное отношение
{-# OPTIONS --cubical --warning=noUnsupportedIndexedMatch #-}
{-# OPTIONS --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module ExampleBinaryRel {ℓ : Level} (hX : hSet ℓ) where

open import Cubical.Foundations.Powerset using (ℙ; _∈_)
open import Cubical.Foundations.Function using (curry; uncurry)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.FinData using (Fin; zero; suc; one; two; three; four; five; toℕ)
open import Cubical.Data.Sigma using (_×_; _,_; ∃; ∃-syntax)
open import Cubical.Data.Vec using (Vec; _∷_; []; lookup) 
open import Cubical.HITs.PropositionalTruncation using (squash₁) 

open import Base

--== Теории бинарных отношений ==--

open РодСтруктуры (hX ∷ []) 

X = ⟨ hX ⟩
S = Ступень (𝔅 (𝔇 (base zero ∷ base zero ∷ [])))

_ : S ≡ ℙ (X × X)
_ = refl

-- Различные бинарные отношения являются элементами S.


--== порождение множества рефлексивных отношений ==--

-- Можно также воспользоваться операцией →𝔅, но сделаем иначе для наглядности.

-- для упрощения используем PropRel, отличный от библиотечного
PropRel : ∀ {ℓX ℓY} (X : Type ℓX) (Y : Type ℓY) (ℓ : Level) → Type _
PropRel X Y ℓ = X → Y → hProp ℓ

-- условие рефлексивности для отношения
IsRefl : ∀ {ℓ ℓ'} {X : Type ℓ} (R : PropRel X X ℓ') → Type _
IsRefl R = ∀ x → fst (R x x)

-- условие рефлексивности для множества пар (uncurry)
IsRefl× : ∀ {ℓ} {X : Type ℓ} (R× : ℙ (X × X)) → hProp _
IsRefl× {ℓ} {X} R× = (∃[ R ∈ PropRel X X ℓ ] (IsRefl R) × (R× ≡ uncurry R))
                   , squash₁

-- Множество рефлексивных отношений (элемент нужной ступени)
-- равен условию рефлексивности! Что неудивительно, поскольку
-- то и другое представляют собой один и тот же предикат.
s : ∀ {Sh : СхемаСтупени 1} → Ступень (𝔅 (𝔅 (𝔇 (Sh ∷ Sh ∷ []))))
s = IsRefl× 

-- Т.е. в теории типов вместо подмножеств декартовых произведений используются
-- каррированные варианты их характеристических функций.

-- Немного другой способ.
-- Определим тип рефлексивных отношений на X:
ReflRel : ∀ {ℓ ℓ'} (X : Type ℓ) → Type _
ReflRel {ℓ} {ℓ'} X = Σ[ R ∈ PropRel X X ℓ' ] IsRefl R

IsRefl×' : ∀ {ℓ} {X : Type ℓ} (R× : ℙ (X × X)) → hProp _
IsRefl×' {ℓ} {X} R× = (∃[ R ∈ ReflRel {ℓ} {ℓ} X ] R× ≡ uncurry (fst R)) , squash₁

s' : ∀ {Sh : СхемаСтупени 1} → Ступень (𝔅 (𝔅 (𝔇 (Sh ∷ Sh ∷ []))))
s' = IsRefl×' 
  

