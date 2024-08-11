{-# OPTIONS --safe #-}

module Cheshire.Homomorphism.Core where

open import Cheshire.Core

private
  variable
    o ℓ o′ ℓ′ : 𝕃.t

record Morphism (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  no-eta-equality
  constructor mkM
  open Quiver 𝒮
  open Quiver 𝒯 renaming (_⇒_ to _⇒ₜ_)

  field
    F₀ : 𝒮 .Ob → 𝒯 .Ob
    F₁ : ∀ {A B} → A ⇒ B → F₀ A ⇒ₜ F₀ B

  ₀ = F₀
  ₁ = F₁
