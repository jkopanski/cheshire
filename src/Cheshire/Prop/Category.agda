{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Prop.Category where

import Cheshire.Signatures as Signature

open import Data.Product.Base using (Σ-syntax)

open Signature using (_[_∘_])

private
  variable
    o ℓ : 𝕃.t
    e j e₁ e₂ : 𝕃.t
    𝒬 : Quiver o ℓ


record Category
  (𝒞 : Signature.Category 𝒬)
  (R : HomPred 𝒬 e)
    : Set (𝕃.levelOfTerm 𝒬 ⊔ e) where
  no-eta-equality
  infixr 9 _∘_
  private
    module C = Signature.Category 𝒞

  field
    id  : ∀ {A} → R (C.id {A = A})
    _∘_ :
      ∀ {A B C} → {g : 𝒬 .Hom B C} {f : 𝒬 .Hom A B} →
      R g → R f → R (𝒞 [ g ∘ f ])


infixr 7 _∩_
_∩_ :
  ∀ {𝒬 : Quiver o ℓ} {R₁ : HomPred 𝒬 e₁} {R₂ : HomPred 𝒬 e₂} {𝒞 : Signature.Category 𝒬} →
  Category 𝒞 R₁ → Category 𝒞 R₂ → Category 𝒞 (R₁ Rel₁.∩ R₂)
P₁ ∩ P₂ = record
  { id = P₁.id , P₂.id
  ; _∘_ = ×.zip P₁._∘_ P₂._∘_
  } where module P₁ = Category P₁
          module P₂ = Category P₂

infix 10 ⋂
⋂ :
  ∀ {𝒬 : Quiver o ℓ} {𝒞 : Signature.Category 𝒬} {J : Set j} →
  (H : J → Σ[ R ∈ HomPred 𝒬 e ] Category 𝒞 R) →
  Category 𝒞 (Rel₁.⋂ J λ j → H j .proj₁)
⋂ H = record
  { id = λ j → id (H j .proj₂)
  ; _∘_ = λ G F → λ j → _∘_ (H j .proj₂) (G j) (F j)
  } where open Category
