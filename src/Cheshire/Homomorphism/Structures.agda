{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Homomorphism.Core

module Cheshire.Homomorphism.Structures
  {o ℓ o′ ℓ′} {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (ℳ : Morphism 𝒮 𝒯)
  where

open Morphism ℳ

open import Cheshire.Signatures

-- IsHomomorphism ?
record IsMorphism {e e′}
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′) :
  Set (o ⊔ ℓ ⊔ e ⊔ e′) where
  open Quiver 𝒮
  open Equivalence eqₛ renaming (_≈_ to _≈ₛ_)
  open Equivalence eqₜ renaming (_≈_ to _≈ₜ_)
  field
    F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ₛ g → F₁ f ≈ₜ F₁ g

record IsFunctor {e e′}
  (S : Category 𝒮) (T : Category 𝒯)
  (eqₛ : Equivalence 𝒮 e)
  (eqₜ : Equivalence 𝒯 e′) :
  Set (o ⊔ ℓ ⊔ e ⊔ e′) where
  open Quiver 𝒮
  open Category S renaming (id to idₛ)
  open Category T renaming (id to idₜ; _∘_ to _∘ₜ_)
  open Equivalence eqₛ renaming (_≈_ to _≈ₛ_)
  open Equivalence eqₜ renaming (_≈_ to _≈ₜ_)
  field
    F-resp-id : ∀ {A} → F₁ (idₛ {A}) ≈ₜ idₜ
    F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
               F₁ (g ∘ f) ≈ₜ F₁ g ∘ₜ F₁ f
    F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ₛ g → F₁ f ≈ₜ F₁ g

  isMorphism : IsMorphism eqₛ eqₜ
  isMorphism = record { F-resp-≈ = F-resp-≈ }
