{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Prop where

import Algebra.Core as Algebra
import Algebra.Morphism.Definitions as Definitions
import Cheshire.Signatures as Signature
open import Data.Product.Base using (Σ-syntax)
open Signature using (_[_∘_])

HomPred : ∀ {o ℓ} → Quiver o ℓ → (e : 𝕃.t) → Set (o ⊔ ℓ ⊔ 𝕃.suc e)
HomPred 𝒬 e = ∀ {A B} → Rel₁.Pred (𝒬 .Hom A B) e

module HomPred {o ℓ e e′} (𝒬 : Quiver o ℓ) where
  _∩_ : HomPred 𝒬 e → HomPred 𝒬 e′ → HomPred 𝒬 (e ⊔ e′)
  P ∩ Q = P Rel₁.∩ Q

private
  variable
    o ℓ : 𝕃.t
    e i j e₁ e₂ : 𝕃.t
    𝒬 : Quiver o ℓ
    R R₁ R₂ : HomPred 𝒬 e


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

  field
    !     : ∀ {A}     → R (C.! {A = A})
    π₁    : ∀ {A B}   → R (C.π₁ {A = A} {B = B})
    π₂    : ∀ {A B}   → R (C.π₂ {A = A} {B = B})
    ⟨_,_⟩ : ∀ {A B D} → {f : 𝒬 .Hom D A} {g : 𝒬 .Hom D B} → R f → R g → R C.⟨ f , g ⟩


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
