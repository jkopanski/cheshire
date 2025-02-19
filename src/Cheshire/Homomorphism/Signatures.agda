{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism.Signatures where

open Function using (_⊙_)

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : 𝕃.t

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

open Morphism public

{-# DISPLAY ₀ F = F₀ F #-}
{-# DISPLAY ₁ F = F₁ F #-}

id : ∀ {A : Quiver o ℓ} → Morphism A A
id .F₀ = Function.id
id .F₁ = Function.id

infixr 9 _∘_
_∘_ :
  ∀ {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″} →
  Morphism B C → Morphism A B → Morphism A C
_∘_ G F .F₀ = G .F₀ ⊙ F .F₀
_∘_ G F .F₁ = G .F₁ ⊙ F .F₁
