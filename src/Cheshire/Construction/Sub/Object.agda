{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Sub.Object {o ℓ} (𝒰 : Quiver o ℓ) where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object

private
  variable
    i : 𝕃.t
    I : Set i

𝒬 : (U : I → 𝒰 .Ob) → Quiver _ ℓ
𝒬 U = mk⇒ λ a b → 𝒰 [ U a , U b ]

module Signatures {U : I → 𝒰 .Ob} where

  open Object

  H : Morphism.t (𝒬 U) 𝒰
  H = record
    { F₀ = U
    ; F₁ = Function.id
    }

  category : (𝒞 : Category.Signature 𝒰) → Category.Signature (𝒬 U)
  category 𝒞 = record
    { id = id
    ; _∘_ = _∘_
    } where open Category.Signature 𝒞

  cartesian :
    {𝒞 : Category.Signature 𝒰} →
    (C : Cartesian.Signature 𝒞) (let open Cartesian.Signature C)
    ⦃ _ : Terminal (𝒬 U .Ob) ⦄ ⦃ _ : BinaryProducts (𝒬 U .Ob) ⦄ →
    Morphism.Terminal H → Morphism.BinaryProducts H →
    Cartesian.Signature (category 𝒞)
  cartesian {𝒞} C tH pH = record
    { terminal = _
    ; ! = tH.⊤-iso.from ∘ !
    ; products = _
    ; π₁ = π₁ ∘ pH.×-iso.to
    ; π₂ = π₂ ∘ pH.×-iso.to
    ; ⟨_,_⟩ = λ f g → pH.×-iso.from ∘ ⟨ f , g ⟩
    } where open Category.Signature 𝒞
            open Cartesian.Signature C
            module tH = Morphism.Terminal tH
            module pH = Morphism.BinaryProducts pH
