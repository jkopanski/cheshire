{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Homomorphism.Signatures

module Cheshire.Homomorphism.Structures
  {o ℓ o′ ℓ′} {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (ℳ : Morphism 𝒮 𝒯)
  where

import Data.Product as ×

open import Cheshire.Signatures
import Cheshire.Object.Signatures as Ob
import Cheshire.Morphism.Bundles as Bundles

open Ob
open Morphism ℳ

module _ {e e′}
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′) where

  instance
    _ = eqₛ; _ = eqₜ

  -- IsHomomorphism ?
  record IsMorphism : Set (o ⊔ ℓ ⊔ e ⊔ e′) where
    open Quiver 𝒮
    field
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → F₁ f ≈ F₁ g

  record IsFunctor
    (S : Category 𝒮) (T : Category 𝒯) :
    Set (o ⊔ ℓ ⊔ e ⊔ e′) where
    open Quiver 𝒮
    module S = Category S
    module T = Category T
    open T using (_∘_)
    field
      F-resp-id : ∀ {A} → F₁ (S.id {A}) ≈ T.id
      F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
                 F₁ (g S.∘ f) ≈ F₁ g ∘ F₁ f
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → F₁ f ≈ F₁ g

    isMorphism : IsMorphism
    isMorphism = record { F-resp-≈ = F-resp-≈ }

  record IsCartesian
    (S : Cartesian 𝒮) (T : Cartesian 𝒯)
    : Set (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′) where
    open Quiver 𝒮
    module S = Cartesian S
    module T = Cartesian T
    open T using (_∘_)
    open Bundles T.category
    private instance
      _ = S.terminal; _ = T.terminal
      _ = S.products; _ = T.products
    field
      -- This is actually something different in agda-categories.  It's
      -- a lawful ⊤ and × moved to the target category.
      -- F-resp-⊤ : ⊤ ≅ F₀ ⊤
      -- F-resp-× : ∀ {A B} → F₀ A × F₀ B ≅ F₀ (A × B)

      ⊤-iso : ⊤ ≅ F₀ ⊤
      ×-iso : ∀ (A B : 𝒮 .Ob) → F₀ A × F₀ B ≅ F₀ (A × B )

      F-resp-id : ∀ {A} → F₁ (S.id {A}) ≈ T.id
      F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
                 F₁ (g S.∘ f) ≈ F₁ g ∘ F₁ f
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → F₁ f ≈ F₁ g

    module ⊤-iso = _≅_ ⊤-iso
    module ×-iso {A B} = _≅_ (×-iso A B)

    field
      F-resp-! : ∀ {A} → ⊤-iso.to ∘ F₁ (S.! {A}) ≈ T.!
      F-resp-⟨⟩ : ∀ {A B X} → (f : X ⇒ A) → (g : X ⇒ B) → ×-iso.to ∘ F₁ S.⟨ f , g ⟩ ≈ T.⟨ F₁ f , F₁ g ⟩
      F-resp-π₁ : ∀ {A B} → F₁ (S.π₁ {A} {B}) ∘ ×-iso.from ≈ T.π₁
      F-resp-π₂ : ∀ {A B} → F₁ (S.π₂ {A} {B}) ∘ ×-iso.from ≈ T.π₂

    isFunctor : IsFunctor S.category T.category
    isFunctor = record
      { F-resp-id = F-resp-id; F-resp-∘ = F-resp-∘; F-resp-≈ = F-resp-≈ }

    isMorphism : IsMorphism
    isMorphism = record { F-resp-≈ = F-resp-≈ }
