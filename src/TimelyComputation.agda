{-# OPTIONS --safe --without-K #-}
module TimelyComputation where

open import Level using (_⊔_; Level)
open import Data.Rational using (ℚ)

private
  variable
    o : Level
    obj : Set o

𝕋 : Set
𝕋 = ℚ

record Boolean (obj : Set o) : Set o where
  field
    𝔹 : obj
open Boolean ⦃ ... ⦄ public

open import Data.Bool using (Bool)
open import Felix.Object using (⊤; _×_; Products)
open import Data.Unit as U using ()
open import Data.Product as P using ()

instance
  BooleanSet : Boolean Set
  𝔹 ⦃ BooleanSet ⦄ = Bool

  ProductsSet : Products Set
  ⊤   ⦃ ProductsSet ⦄ = U.⊤
  _×_ ⦃ ProductsSet ⦄ = P._×_

𝕊 : ⦃ Boolean obj ⦄ → Set
𝕊 = 𝕋 → 𝔹

_⁰ : ⦃ Products obj ⦄ → obj → obj 
_ ⁰ = ⊤

_² : ⦃ Products obj ⦄ → obj → obj
A ² = A × A

-- dup : ∀ {a} → {A : Set a} → A → A × A
-- dup a = a , a

open import Data.Rational using (_-_)

analog₀ : ⦃ Boolean obj ⦄ → ⦃ Products obj ⦄ → 𝕋 ⁰ → (𝔹 ⁰ → 𝔹) → (𝕊 ⁰ → 𝕊)
analog₀ tt h tt = λ t → h tt

analog₁ : 𝕋 → (𝔹 → 𝔹) → (𝕊 → 𝕊)
analog₁ δ h x̃ = λ t → h (x̃ (t - δ))

-- analog₂ : 𝕋 ² → (𝔹 ² → 𝔹) → (𝕊 ² → 𝕊)
-- analog₂ (δ₁ , δ₂) h (x̃₁ , x̃₂) = λ t → h (x̃₁ (t - δ₁) , x̃₂ (t - δ₂))

open import Data.Integer using (+_)
open import Data.Unit using (tt)
open import Data.Rational using (_/_)
open import Data.Nat using () -- For NonZero-ness of rational denominators

δ-false = tt
δ-true = tt
δ-not = + 1 / 10
-- δ-nand = dup (+ 1 / 5)
-- δ-nor = dup (+ 1 / 5)
-- δ-xor = dup (+ 1 / 4)

open import Felix.Raw using (Category; _∘_)

record Logic ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
             {ℓ} (_⇨′_ : obj → obj → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    false true : ⊤ ⇨ 𝔹
    not : 𝔹 ⇨ 𝔹
    nand nor xor : 𝔹 × 𝔹 ⇨ 𝔹
  and or : ⦃ Category _⇨_ ⦄ → 𝔹 × 𝔹 ⇨ 𝔹
  and = not ∘ nand
  or  = not ∘ nor
open Logic ⦃ ... ⦄ public

-- nandᴬ : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄ ⦃ _ : Logic {o} {obj} _ ⦄ → 𝕊 ² → 𝕊
-- nandᴬ = analog₂ δ-nand nand
