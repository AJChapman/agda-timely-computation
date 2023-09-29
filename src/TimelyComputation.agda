{-# OPTIONS --safe --without-K #-}
module TimelyComputation where

open import Data.Rational using (ℚ)

𝕋 : Set
𝕋 = ℚ

record Boolean {o} (obj : Set o) : Set o where
  field
    𝔹 : obj
open Boolean ⦃ ... ⦄ public

open import Data.Bool using (Bool)

instance
  boolean : Boolean Set
  boolean = record { 𝔹 = Bool }

open import Level as L using ()

𝕊 : ∀ {o} → {obj : Set o} → ⦃ Boolean obj ⦄ → Set
𝕊 = 𝕋 → 𝔹

open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_)

_⁰ : Set → Set
_ ⁰ = ⊤

_² : Set → Set
A ² = A × A

dup : {A : Set} → A → A × A
dup a = a , a

open import Data.Rational using (_-_)

analog₀ : 𝕋 ⁰ → (𝔹 ⁰ → 𝔹) → (𝕊 ⁰ → 𝕊)
analog₀ tt h tt = λ t → h tt

analog₁ : 𝕋 → (𝔹 → 𝔹) → (𝕊 → 𝕊)
analog₁ δ h x̃ = λ t → h (x̃ (t - δ))

analog₂ : 𝕋 ² → (𝔹 ² → 𝔹) → (𝕊 ² → 𝕊)
analog₂ (δ₁ , δ₂) h (x̃₁ , x̃₂) = λ t → h (x̃₁ (t - δ₁) , x̃₂ (t - δ₂))

open import Data.Integer using (+_)
open import Data.Unit using (tt)
open import Data.Rational using (_/_)
open import Data.Nat using () -- For NonZero-ness of rational denominators

δ-false = tt
δ-true = tt
δ-not = + 1 / 10
δ-nand = dup (+ 1 / 5)
δ-nor = dup (+ 1 / 5)
δ-xor = dup (+ 1 / 4)

open import Level using (_⊔_)
open import Felix.Raw using (Category)
open Category using (_∘_)
open import Felix.Object as F using (Products)

record Logic {o} {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
             {ℓ} (_⇨′_ : obj → obj → Set ℓ) ⦃ _ : Category _⇨′_ ⦄ : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    false true : F.⊤ ⇨ 𝔹
    not : 𝔹 ⇨ 𝔹
    nand nor xor : 𝔹 F.× 𝔹 ⇨ 𝔹
  -- and or : 𝔹 F.× 𝔹 ⇨ 𝔹
  -- and = not ∘ nand
  -- or  = not ∘ nor
open Logic ⦃ ... ⦄ public

-- nandᴬ : 𝕊 ² → 𝕊
-- nandᴬ = analog₂ δ-nand nand
