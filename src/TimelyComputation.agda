{-# OPTIONS --safe --without-K #-}
module TimelyComputation where

open import Level using (_⊔_; Level)
open import Function using (const)
open import Data.Bool as B using (Bool)
open import Data.Integer using (+_)
open import Data.Nat using () -- For NonZero-ness of rational denominators
open import Data.Product as P using (_,_)
open import Data.Rational using (ℚ; _/_; _-_)
open import Data.Unit.Polymorphic using (tt)

open import Felix.Object using (⊤; _×_; Products)
open import Felix.Instances.Function.Type Level.zero using (_⇾_; module →-instances)
open import Felix.Instances.Function.Raw Level.zero using (module →-raw-instances)
open import Felix.Raw using (Category; _∘_; Cartesian; dup; CartesianClosed)

private
  variable
    o ℓ : Level
    obj : Set o

𝕋 : Set
𝕋 = ℚ

record Boolean (obj : Set o) : Set o where
  field
    𝔹 : obj
open Boolean ⦃ ... ⦄ public

instance
  BooleanSet : Boolean Set
  𝔹 ⦃ BooleanSet ⦄ = Bool

𝕊 : ⦃ Boolean obj ⦄ → Set
𝕊 = 𝕋 → 𝔹

_⁰ : ⦃ Products obj ⦄ → obj → obj 
_ ⁰ = ⊤

_² : ⦃ Products obj ⦄ → obj → obj
A ² = A × A

analog₀ : 𝕋 ⁰ → (𝔹 ⁰ → 𝔹) → (𝕊 ⁰ → 𝕊)
analog₀ tt h tt = λ t → h tt

analog₁ : 𝕋 → (𝔹 → 𝔹) → (𝕊 → 𝕊)
analog₁ δ h x̃ = λ t → h (x̃ (t - δ))

analog₂ : 𝕋 ² → (𝔹 ² → 𝔹) → (𝕊 ² → 𝕊)
analog₂ (δ₁ , δ₂) h (x̃₁ , x̃₂) = λ t → h (x̃₁ (t - δ₁) , x̃₂ (t - δ₂))

δ-false δ-true : 𝕋 ⁰
δ-false = tt
δ-true = tt

δ-not : 𝕋
δ-not = + 1 / 10

δ-nand : 𝕋 ²
δ-nand = dup (+ 1 / 5)
δ-nor = dup (+ 1 / 5)
δ-xor = dup (+ 1 / 4)

record Logic {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
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

instance
  SetLogic : Logic _⇾_
  false ⦃ SetLogic ⦄ = const B.false
  true  ⦃ SetLogic ⦄ = const B.true
  not   ⦃ SetLogic ⦄ = B.not
  nand  ⦃ SetLogic ⦄ = not ∘ (P.uncurry B._∧_)
  nor   ⦃ SetLogic ⦄ = not ∘ (P.uncurry B._∨_)
  xor   ⦃ SetLogic ⦄ = P.uncurry B._xor_
  
nandᴬ : 𝕊 ² → 𝕊
nandᴬ = analog₂ δ-nand nand
    