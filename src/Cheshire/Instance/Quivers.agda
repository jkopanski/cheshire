{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Quivers where

import Data.Product.Base using (Σ-syntax; Σ; ∃)
import Relation.Binary.Construct.On as On

import Cheshire.Category.Signature as Signature renaming (Category to t)
import Cheshire.Category.Structure as Structure renaming (IsCategory to t)
import Cheshire.Category.Bundle as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)

open Function using (_on₂_)
open Morphism using (Homomorphism; _≃_; ≃-isEquivalence)
open Homomorphism

record Enriched o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  no-eta-equality
  pattern
  constructor mk
  field
    𝒬      : Quiver o ℓ
    instance ⦃ eq ⦄ : Equivalence 𝒬 e

⌞_⌟ : ∀ {o ℓ e} → Enriched o ℓ e → Quiver o ℓ
⌞_⌟ = Enriched.𝒬

𝒬 : ∀ o ℓ e → Quiver (𝕃.suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e)
𝒬 o ℓ e = mk⇒ {Ob = Enriched o ℓ e } λ S T →
  Homomorphism ⌞ S ⌟ ⌞ T ⌟ (S .Enriched.eq) (T .Enriched.eq)

instance
  eq : ∀ {o ℓ e} → Equivalence (𝒬 o ℓ e) (o ⊔ ℓ ⊔ e)
  eq = record
    { _≈_ = λ where
      {mk _} {mk _} → _≃_ on morphism
    ; equiv = λ where
      {mk _} {mk _} → On.isEquivalence morphism ≃-isEquivalence
    }

module _ (o ℓ e : 𝕃.t) where

  category : Signature.t (𝒬 o ℓ e)
  category = record
    { id = λ where
      {mk _} → record
        { morphism = Morphism.id
        ; isHomomorphism = Morphism.id-isHomomorphism
        }
    ; _∘_ = λ where
      {mk _} {mk _} {mk _} g f → record
        { morphism = g .morphism Morphism.∘ f .morphism
        ; isHomomorphism = Morphism.∘-isHomomorphism (g .isHomomorphism) (f .isHomomorphism)
        }
    }
  open Signature.t category

  is-category : Structure.t eq category
  is-category = record
    { assoc = λ where
      {mk _} {mk _} {mk _} {mk _ ⦃ eq ⦄} {f} {g} {h} → record { F₀≡ = ≡-refl ; F₁≡ = eq .refl }
    ; identityʳ = λ where
      {mk _} {mk _ ⦃ eq ⦄} → record { F₀≡ = ≡-refl ; F₁≡ = eq .refl }
    ; identityˡ = λ where
      {mk _} {mk _ ⦃ eq ⦄} → record { F₀≡ = ≡-refl ; F₁≡ = eq .refl }
    ; ∘-resp-≈ = λ where
      {mk _} {mk _} {mk _} {h = h} → Morphism.≃-resp-∘ (h .isHomomorphism)
    }

  Quivers : Category.t (𝕃.suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  Quivers = record
    { 𝒬 = 𝒬 o ℓ e
    ; category = category
    ; isCategory = is-category
    }
