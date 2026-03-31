{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Construction.Sub.Morphism {o ℓ} (𝒰 : Quiver o ℓ) where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Prop as Prop
import Cheshire.Object.Signatures as Object

open × using (Σ-syntax)
open Function using (_-⟨_⟩-_)
private
  variable
    e : 𝕃.t

𝒬 : (R : ∀ {A B} → Rel₁.Pred (𝒰 .Hom A B) e) → Quiver o (ℓ ⊔ e)
𝒬 R = mk⇒ λ X Y → Σ[ f ∈ 𝒰 .Hom X Y ] (R f)

module Signatures {R : ∀ {A B} → Rel₁.Pred (𝒰 .Hom A B) e} where

  H : Morphism.t (𝒬 R) 𝒰
  H = record
    { F₀ = Function.id
    ; F₁ = ×.proj₁
    }

  category : {𝒞 : Category.Signature 𝒰} (P : Prop.Category R 𝒞) → Category.Signature (𝒬 R)
  category {𝒞} P = record
    { id = id , P.id
    ; _∘_ = λ (g , gᴿ) (f , fᴿ) → g ∘ f , gᴿ P.∘ fᴿ
    } where open Category.Signature 𝒞
            module P = Prop.Category P

  cartesian :
    {𝒞 : Category.Signature 𝒰} {C : Cartesian.Signature 𝒞} →
    (Cᴿ : Category.Signature (𝒬 R))
    (P : Prop.Cartesian R C) →
    Cartesian.Signature Cᴿ
  cartesian {C = C} Cᴿ P = record
    { terminal = terminal
    ; ! = ! , P.!
    ; products = products
    ; π₁ = π₁ , P.π₁
    ; π₂ = π₂ , P.π₂
    ; ⟨_,_⟩ = λ (f , fᴿ) (g , gᴿ)  → ⟨ f , g ⟩ , P.⟨ fᴿ , gᴿ ⟩
    } where open Category.Signature Cᴿ
            open Cartesian.Signature C
            module P = Prop.Cartesian P

