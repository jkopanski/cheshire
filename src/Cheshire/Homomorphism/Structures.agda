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

-- IsHomomorphism ?
record IsMorphism {e e′}
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′) :
  Set (o ⊔ ℓ ⊔ e ⊔ e′) where
  open Quiver 𝒮
  private instance
    _ = eqₛ; _ = eqₜ
  field
    F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → F₁ f ≈ F₁ g

record IsFunctor {e e′}
  (S : Category 𝒮) (T : Category 𝒯)
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′) :
  Set (o ⊔ ℓ ⊔ e ⊔ e′) where
  open Quiver 𝒮
  module S = Category S
  module T = Category T
  open T using (_∘_)
  private instance
    _ = eqₛ; _ = eqₜ
  field
    F-resp-id : ∀ {A} → F₁ (S.id {A}) ≈ T.id
    F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
               F₁ (g S.∘ f) ≈ F₁ g ∘ F₁ f
    F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → F₁ f ≈ F₁ g

  isMorphism : IsMorphism eqₛ eqₜ
  isMorphism = record { F-resp-≈ = F-resp-≈ }

record IsCartesian {e e′}
  (S : Cartesian 𝒮) (T : Cartesian 𝒯)
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′)
  : Set (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′) where
  open Quiver 𝒮
  module S = Cartesian S
  module T = Cartesian T
  open T using (_∘_)
  open Bundles T.category
  private instance
    _ = eqₛ; _ = eqₜ
    _ = S.terminal; _ = T.terminal
    _ = S.products; _ = T.products
  field
    F-resp-⊤ : ⊤ ≅ F₀ ⊤
    F-resp-× : ∀ {A B} → F₀ A × F₀ B ≅ F₀ (A × B)

    F-resp-id : ∀ {A} → F₁ (S.id {A}) ≈ T.id
    F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
               F₁ (g S.∘ f) ≈ F₁ g ∘ F₁ f
    F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → F₁ f ≈ F₁ g

  module F-resp-⊤ = _≅_ F-resp-⊤
  module F-resp-× {A B} = _≅_ (F-resp-× {A} {B})

  ⊤-iso : Iso ⊤ (F₀ ⊤)
  ⊤-iso .×.proj₁ = record { F-resp-⊤ }
  ⊤-iso .×.proj₂ = record { F-resp-⊤ }

  ×-iso : ∀ (A B : Ob) → Iso (F₀ A × F₀ B) (F₀ (A × B ))
  ×-iso A B .×.proj₁ = record { F-resp-× }
  ×-iso A B .×.proj₂ = record { F-resp-× }

  isFunctor : IsFunctor S.category T.category eqₛ eqₜ
  isFunctor = record
    { F-resp-id = F-resp-id; F-resp-∘ = F-resp-∘; F-resp-≈ = F-resp-≈ }

  isMorphism : IsMorphism eqₛ eqₜ
  isMorphism = record { F-resp-≈ = F-resp-≈ }
