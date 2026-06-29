{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Prop.Cartesian where

import Cheshire.Signatures as Signature
import Cheshire.Prop.Category as Category renaming (Category to t)
open import Data.Product.Base using (Σ-syntax)

private
  variable
    o ℓ : 𝕃.t
    e j e₁ e₂ : 𝕃.t
    𝒬 : Quiver o ℓ


record Cartesian
  {𝒬 : Quiver o ℓ}
  {𝒞 : Signature.Category 𝒬}
  (C : Signature.Cartesian 𝒞)
  (R : HomPred 𝒬 e)
    : Set (𝕃.levelOfTerm 𝒬 ⊔ e) where
  no-eta-equality
  infix 11 ⟨_,_⟩
  private
    module C = Signature.Cartesian C

  -- Is this really needed?
  -- I think it is convenient.
  field
    category : Category.t 𝒞 R

  field
    !     : ∀ {A}     → R (C.! {A = A})
    π₁    : ∀ {A B}   → R (C.π₁ {A = A} {B = B})
    π₂    : ∀ {A B}   → R (C.π₂ {A = A} {B = B})
    ⟨_,_⟩ : ∀ {A B D} → {f : 𝒬 .Hom D A} {g : 𝒬 .Hom D B} → R f → R g → R C.⟨ f , g ⟩


infixr 7 _∩_
_∩_ :
  ∀ {𝒬 : Quiver o ℓ} {R₁ : HomPred 𝒬 e₁} {R₂ : HomPred 𝒬 e₂} →
  ∀ {𝒞 : Signature.Category 𝒬} {C : Signature.Cartesian 𝒞} →
  Cartesian C R₁ → Cartesian C R₂ → Cartesian C (R₁ Rel₁.∩ R₂)
P₁ ∩ P₂ = record
  { category = P₁.category Category.∩ P₂.category
  ; ! = P₁.! , P₂.!
  ; π₁ = P₁.π₁ , P₂.π₁
  ; π₂ = P₁.π₂ , P₂.π₂
  ; ⟨_,_⟩ = ×.zip P₁.⟨_,_⟩ P₂.⟨_,_⟩
  } where module P₁ = Cartesian P₁
          module P₂ = Cartesian P₂

infix 10 ⋂
⋂ :
  ∀ {𝒬 : Quiver o ℓ} {𝒞 : Signature.Category 𝒬} {C : Signature.Cartesian 𝒞} {J : Set j} →
  (H : J → Σ[ R ∈ HomPred 𝒬 e ] Cartesian C R) →
  Cartesian C (Rel₁.⋂ J λ j → H j .proj₁)
⋂ H = record
  { category = Category.⋂ (×.map₂ category ⊙ H)
  ; ! = λ j → ! (H j .proj₂)
  ; π₁ = λ j → π₁ (H j .proj₂)
  ; π₂ = λ j → π₂ (H j .proj₂)
  ; ⟨_,_⟩ = λ G F → λ j → ⟨_,_⟩ (H j .proj₂) (G j) (F j)
  } where open Cartesian
