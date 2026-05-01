{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism where

import Data.Product as ×
open import Relation.Binary.PropositionalEquality.Subst.Properties
  using (module Shorthands; module Transport; module TransportOverQ)
import Cheshire.Category.Signature as Category renaming (Category to t)

open import Cheshire.Homomorphism.Signatures public
open import Cheshire.Homomorphism.Structures public
open import Cheshire.Homomorphism.Bundles public

-- Copied from agda-categories:
-- https://agda.github.io/agda-categories/Data.Quiver.Morphism.html#2527
-- which is licensed under the MIT license.
--   Copyright (c) 2019 Agda Github Community

open × using (Σ-syntax)
open Rel₂ using (_≡_; Reflexive; Symmetric; Transitive)

private
  variable
    o ℓ o′ ℓ′ e′ o″ ℓ″ : 𝕃.t

infix 4 _≃_
record _≃_
  {𝒬 : Quiver o ℓ} {𝒬′ : Quiver o′ ℓ′}
  ⦃ eq : Equivalence 𝒬′ e′ ⦄
  (ℳ ℳ′ : Morphism 𝒬 𝒬′)
  : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module M  = Morphism ℳ
    module M′ = Morphism ℳ′
  open Shorthands (𝒬′ .Hom)

  field
    F₀≡ : ∀ {X} → M.₀ X ≡ M′.₀ X
    F₁≡ : ∀ {A B} {f : 𝒬 .Hom A B} → M.₁ f ▸ F₀≡ ≈ F₀≡ ◂ M′.₁ f

module _
  {𝒬 : Quiver o ℓ} {𝒬′ : Quiver o ℓ}
  -- {e}  ⦃ eq  : Equivalence 𝒬  e  ⦄
  {e} ⦃ eq : Equivalence 𝒬′ e ⦄
  where
  open _≃_
  -- open Equivalence eq

  private
    open EdgeReasoning
    open Transport (𝒬′ .Hom)
    open TransportOverQ (𝒬′ .Hom) (eq ._≈_)

    ≃-refl : Reflexive {A = Morphism 𝒬 𝒬′} _≃_
    ≃-refl = record { F₀≡ = ≡-refl; F₁≡ = refl }

    ≃-sym : Symmetric {A = Morphism 𝒬 𝒬′} _≃_
    ≃-sym {x} {y} x≃y = record
      { F₀≡ = ≡-sym e₁
      ; F₁≡ = λ {_ _ f} →
        begin
          F₁ y f ▸ ≡-sym e₁
        ≡⟨ ≡-cong (_◂ (F₁ y f ▸ ≡-sym e₁)) (Rel₂.trans-symˡ e₁) ⟨
          ≡-trans (≡-sym e₁) e₁ ◂ (F₁ y f ▸ ≡-sym e₁)
        ≡⟨ ◂-assocˡ (≡-sym e₁) (F₁ y f ▸ ≡-sym e₁) ⟨
          ≡-sym e₁ ◂ e₁ ◂ (F₁ y f ▸ ≡-sym e₁)
        ≡⟨ ≡-cong (≡-sym e₁ ◂_) (◂-▸-comm e₁ (F₁ y f) (≡-sym e₁)) ⟩
          ≡-sym e₁ ◂ ((e₁ ◂ F₁ y f) ▸ ≡-sym e₁)
        ≈⟨ ◂-resp-≈ (≡-sym e₁) (▸-resp-≈ (x≃y .F₁≡) (≡-sym e₁)) ⟨
          ≡-sym e₁ ◂ (F₁ x f ▸ e₁ ▸ ≡-sym e₁)
        ≡⟨ ≡-cong (≡-sym e₁ ◂_) (▸-assocʳ (F₁ x f) (≡-sym e₁)) ⟩
          ≡-sym e₁ ◂ (F₁ x f ▸ ≡-trans e₁ (≡-sym e₁))
        ≡⟨ ≡-cong (λ p → ≡-sym e₁ ◂ (F₁ x f ▸ p)) (Rel₂.trans-symʳ e₁) ⟩
          ≡-sym e₁ ◂ F₁ x f
        ∎
      } where e₁ = F₀≡ x≃y

    ≃-trans : Transitive {A = Morphism 𝒬 𝒬′} _≃_
    ≃-trans {i} {j} {k} i≃j j≃k = record
      { F₀≡ = ≡-trans (F₀≡ i≃j) (F₀≡ j≃k)
      ; F₁≡ = λ {_ _ f} → begin
        F₁ i f ▸ ≡-trans (F₀≡ i≃j) (F₀≡ j≃k) ≡⟨ ▸-assocʳ (F₁ i f) (F₀≡ j≃k) ⟨
        (F₁ i f ▸ F₀≡ i≃j) ▸ F₀≡ j≃k         ≈⟨ ▸-resp-≈ (F₁≡ i≃j) (F₀≡ j≃k) ⟩
        (F₀≡ i≃j ◂ F₁ j f) ▸ F₀≡ j≃k         ≡⟨ ◂-▸-comm (F₀≡ i≃j) (F₁ j f) (F₀≡ j≃k) ⟨
        F₀≡ i≃j ◂ (F₁ j f ▸ F₀≡ j≃k)         ≈⟨ ◂-resp-≈ (F₀≡ i≃j) (F₁≡ j≃k) ⟩
        F₀≡ i≃j ◂ (F₀≡ j≃k ◂ F₁ k f)         ≡⟨ ◂-assocˡ (F₀≡ i≃j) (F₁ k f) ⟩
        ≡-trans (F₀≡ i≃j) (F₀≡ j≃k) ◂ F₁ k f ∎
      }

  ≃-Equivalence : Rel₂.IsEquivalence _≃_
  ≃-Equivalence = record
    { refl  = ≃-refl
    ; sym   = ≃-sym
    ; trans = ≃-trans
    }

module _
  {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″}
  ⦃ eq : Equivalence C e′ ⦄
  where

  infix 5 _∣ˡ_
  _∣ˡ_ : Morphism B C → Morphism A C → Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  G ∣ˡ F = Σ[ J ∈ Morphism A B ] G ∘ J ≃ F

id-isHomomorphism : {𝒬 : Quiver o ℓ} → ⦃ eq : Equivalence 𝒬 e′ ⦄ → IsHomomorphism eq eq id
id-isHomomorphism = record { F-resp-≈ = Function.id }

id-isFunctor :
  {𝒬 : Quiver o ℓ} → (C : Category.t 𝒬) →
  ⦃ eq : Equivalence 𝒬 e′ ⦄ →
  IsFunctor eq eq C C id
id-isFunctor _ = record
  { F-resp-id = refl
  ; F-resp-∘ = refl
  }

