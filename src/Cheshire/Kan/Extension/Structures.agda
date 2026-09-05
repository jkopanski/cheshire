{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Extension.Structures where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Homomorphism renaming (Morphism to t)
import Cheshire.Natural as Natural

open import Cheshire.Kan.Extension.Signatures as Signatures

open Homomorphism using (_∘_)
open Natural.Signatures

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : 𝕃.t

module _
  {A : Quiver o ℓ}
  {B : Quiver o′ ℓ′}
  {C : Quiver o″ ℓ″}
  (𝒞 : Category.t C)
  (eq : Equivalence C e″)
  {F : Homomorphism.t A B} {X : Homomorphism.t A C}
  where

  open Natural.Equivalence {𝒮 = A} {𝒯 = C} eq renaming (_≃_ to _≃ᵃ_)
  open Natural.Equivalence {𝒮 = B} {𝒯 = C} eq
  open Natural.Signatures.Compose 𝒞

  record IsLan (lan : Lan F X) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    open Lan lan
    field
      σ-unique :
        {M : Homomorphism.t B C} → {α : Transformation X (M ∘ F)} →
        (σ′ : Transformation L M) → α ≃ᵃ (σ′ ∘ʳ F) ∘ᵥ η → σ′ ≃ σ M α

      commutes :
        (M : Homomorphism.t B C) → (α : Transformation X (M ∘ F)) →
        α ≃ᵃ (σ M α ∘ʳ F) ∘ᵥ η


  record IsRan (ran : Ran F X) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    open Ran ran
    field
      δ-unique :
        {M : Homomorphism.t B C} → {α : Transformation (M ∘ F) X} → (δ′ : Transformation M R) → α ≃ᵃ ε ∘ᵥ (δ′ ∘ʳ F) → δ′ ≃ δ M α
      commutes :
        (M : Homomorphism.t B C) → (α : Transformation (M ∘ F) X) → α ≃ᵃ ε ∘ᵥ (δ M α ∘ʳ F)
