{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Lift.Structures where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Homomorphism renaming (Morphism to t)
import Cheshire.Natural as Natural

open import Cheshire.Kan.Lift.Signatures as Signatures

open Homomorphism using (_∘_)
open Natural.Signatures

private
  variable
    o ℓ o′ ℓ′ e′ o″ ℓ″ e″ : 𝕃.t

module _
  {A : Quiver o ℓ}
  {B : Quiver o′ ℓ′}
  {C : Quiver o″ ℓ″}
  (ℬ : Category.t B)
  (𝒞 : Category.t C)
  (eqᵇ : Equivalence B e′)
  (eqᶜ : Equivalence C e″)
  {F : Homomorphism.t B C} {X : Homomorphism.t A C}
  where

  open Natural.Equivalence {𝒮 = A} {𝒯 = B} eqᵇ renaming (_≃_ to _≃ᵇ_)
  open Natural.Equivalence {𝒮 = A} {𝒯 = C} eqᶜ
  open Natural.Signatures.Compose 𝒞

  record IsLift (lift : Lift F X) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    open Lift lift
    field
      σ-unique :
        {M : Homomorphism.t A B} → {α : Transformation X (F ∘ M)} →
        (σ′ : Transformation L M) → α ≃ (F ∘ˡ σ′) ∘ᵥ η → σ′ ≃ᵇ σ M α
      commutes :
        (M : Homomorphism.t A B) → (α : Transformation X (F ∘ M)) →
        α ≃ (F ∘ˡ σ M α) ∘ᵥ η


  record IsRift (rift : Rift F X) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    open Rift rift
    field
      δ-unique :
        {M : Homomorphism.t A B} → {α : Transformation (F ∘ M) X} →
        (δ′ : Transformation M R) → α ≃ ε ∘ᵥ (F ∘ˡ δ′) → δ′ ≃ᵇ δ M α
      commutes :
        (M : Homomorphism.t A B) → (α : Transformation (F ∘ M) X) →
        α ≃ ε ∘ᵥ (F ∘ˡ δ M α)

