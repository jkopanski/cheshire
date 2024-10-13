{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Signatures using (Category)

module Cheshire.Morphism.Structures
  {o ℓ} {𝒬 : Quiver o ℓ} (𝒞 : Category 𝒬)
  where

open Quiver 𝒬
open Category 𝒞

private
  variable
    e : 𝕃.t
    A B C : Ob

IsMono : ⦃ Equivalence 𝒬 e ⦄ → ∀ (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
IsMono {A = A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) →
  f ∘ g₁ ≈ f ∘ g₂ → g₁ ≈ g₂

IsEpi : ⦃ Equivalence 𝒬 e ⦄ → ∀ (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
IsEpi {B = B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) →
  g₁ ∘ f ≈ g₂ ∘ f → g₁ ≈ g₂

record IsIso
  ⦃ eq : Equivalence 𝒬 e ⦄ (from : A ⇒ B) (to : B ⇒ A)
  : Set (o ⊔ ℓ ⊔ e) where
  field
    isoˡ : to ∘ from ≈ id
    isoʳ : from ∘ to ≈ id
