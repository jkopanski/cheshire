{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Prop
  {o ℓ} {𝒬 : Quiver o ℓ}
  {e} (R : ∀ {A B} → Rel₁.Pred (𝒬 .Hom A B) e)
  where

import Cheshire.Signatures as Signature
open Quiver 𝒬 using (_⇒_)
open Signature using (_[_∘_])

private
  variable
    A B C D : 𝒬 .Ob

record Category (𝒞 : Signature.Category 𝒬) : Set (o ⊔ ℓ ⊔ e) where
  no-eta-equality
  infixr 9 _∘_
  private
    module C = Signature.Category 𝒞

  field
    id : R (C.id {A = A})
    _∘_ : {g : 𝒬 .Hom B C} {f : 𝒬 .Hom A B} → R g → R f → R (𝒞 [ g ∘ f ])


record Cartesian {𝒞 : Signature.Category 𝒬} (C : Signature.Cartesian 𝒞) : Set (o ⊔ ℓ ⊔ e) where
  no-eta-equality
  infix 11 ⟨_,_⟩
  private
    module C = Signature.Cartesian C

  field
    !     : R (C.! {A = A})
    π₁    : R (C.π₁ {A = A} {B = B})
    π₂    : R (C.π₂ {A = A} {B = B})
    ⟨_,_⟩ : {f : 𝒬 .Hom D A} {g : 𝒬 .Hom D B} → R f → R g → R C.⟨ f , g ⟩
