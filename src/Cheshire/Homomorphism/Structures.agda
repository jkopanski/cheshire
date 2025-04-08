{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Homomorphism.Signatures hiding (_∘_)

module Cheshire.Homomorphism.Structures
  {o ℓ o′ ℓ′} {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (ℳ : Morphism 𝒮 𝒯)
  where

import Data.Product as ×
import Relation.Binary.Construct.On as On

open import Cheshire.Signatures
import Cheshire.Object.Signatures as Ob
import Cheshire.Morphism.Bundles as Bundles

open Ob
private
  module M = Morphism ℳ

module _ {e} (eqₛ : Equivalence 𝒯 e) where
  equivalence : Equivalence 𝒮 e
  equivalence = record
    { _≈_ = _≈_ on M.₁
    ; equiv = On.isEquivalence M.₁ equiv
    } where instance _ = eqₛ

module _ {e e′}
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′)
  where

  private
    instance
      _ = eqₛ
      - = eqₜ

  -- IsHomomorphism ?
  record IsMorphism : Set (o ⊔ ℓ ⊔ e ⊔ e′) where
    open Quiver 𝒮
    field
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → M.₁ f ≈ M.₁ g

    -- for nicer module use: F.resp-≈
    resp-≈ = F-resp-≈

  record IsFunctor
    (S : Category 𝒮) (T : Category 𝒯) :
    Set (o ⊔ ℓ ⊔ e ⊔ e′) where
    open Quiver 𝒮
    module S = Category S
    module T = Category T
    open T using (_∘_)
    field
      F-resp-id : ∀ {A} → M.₁ (S.id {A}) ≈ T.id
      F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
                 M.₁ (g S.∘ f) ≈ M.₁ g ∘ M.₁ f
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → M.₁ f ≈ M.₁ g

    isMorphism : IsMorphism
    isMorphism = record { F-resp-≈ = F-resp-≈ }

    resp-id = F-resp-id
    resp-∘  = F-resp-∘
    resp-≈  = F-resp-≈

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

      ⊤-iso : ⊤ ≅ M.₀ ⊤
      ×-iso : ∀ (A B : 𝒮 .Ob) → M.₀ A × M.₀ B ≅ M.₀ (A × B )

      F-resp-id : ∀ {A} → M.₁ (S.id {A}) ≈ T.id
      F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
                 M.₁ (g S.∘ f) ≈ M.₁ g ∘ M.₁ f
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → M.₁ f ≈ M.₁ g

    module ⊤-iso = _≅_ ⊤-iso
    module ×-iso {A B} = _≅_ (×-iso A B)

    field
      F-resp-! : ∀ {A} → ⊤-iso.to ∘ M.₁ (S.! {A}) ≈ T.!
      F-resp-⟨⟩ : ∀ {A B X} → (f : X ⇒ A) → (g : X ⇒ B) → ×-iso.to ∘ M.₁ S.⟨ f , g ⟩ ≈ T.⟨ M.₁ f , M.₁ g ⟩
      F-resp-π₁ : ∀ {A B} → M.₁ (S.π₁ {A} {B}) ∘ ×-iso.from ≈ T.π₁
      F-resp-π₂ : ∀ {A B} → M.₁ (S.π₂ {A} {B}) ∘ ×-iso.from ≈ T.π₂

    isFunctor : IsFunctor S.category T.category
    isFunctor = record
      { F-resp-id = F-resp-id; F-resp-∘ = F-resp-∘; F-resp-≈ = F-resp-≈ }

    isMorphism : IsMorphism
    isMorphism = record { F-resp-≈ = F-resp-≈ }

    resp-id = F-resp-id
    resp-∘  = F-resp-∘
    resp-≈  = F-resp-≈
