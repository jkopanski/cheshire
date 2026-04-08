{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Sub.Object where

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms

open Object
open Morphisms.Bundles using (Iso)

private
  variable
    o ℓ e i : 𝕃.t
    I : Set i

𝒬 : ∀ {o ℓ i} → {I : Set i} → (𝒰 : Quiver o ℓ) → (U : I → 𝒰 .Ob) → Quiver i ℓ
𝒬 𝒰 U = mk⇒ λ a b → 𝒰 [ U a , U b ]

module _ (𝒯 : Quiver o ℓ) (U : I → 𝒯 .Ob) where

  𝒮 : Quiver _ ℓ
  𝒮 = 𝒬 𝒯 U

  H : Morphism.t 𝒮 𝒯
  H = record
    { F₀ = U
    ; F₁ = Function.id
    }

  private module H = Morphism.t H

  module Signatures (T : Category.Signature 𝒯) where

    open Category.Signature T

    category : Category.Signature 𝒮
    category = record
      { id = id
      ; _∘_ = _∘_
      }

    cartesian :
      (C : Cartesian.Signature T) (let open Cartesian.Signature C)
      ⦃ _ : Terminal (𝒮 .Ob) ⦄ ⦃ _ : BinaryProducts (𝒮 .Ob) ⦄ →
      Morphism.Terminal H → Morphism.BinaryProducts H →
      Cartesian.Signature category
    cartesian C tH pH = record
      { terminal = _
      ; ! = tH.⊤-iso.from ∘ !
      ; products = _
      ; π₁ = π₁ ∘ pH.×-iso.to
      ; π₂ = π₂ ∘ pH.×-iso.to
      ; ⟨_,_⟩ = λ f g → pH.×-iso.from ∘ ⟨ f , g ⟩
      } where open Cartesian.Signature C
              module tH = Morphism.Terminal tH
              module pH = Morphism.BinaryProducts pH

  module Structures ⦃ eqₜ : Equivalence 𝒯 e ⦄ where

    eq : Equivalence 𝒮 e
    eq = Morphism.equivalence eqₜ H

    H-is-homomorphism : Morphism.IsHomomorphism eq eqₜ H
    H-is-homomorphism = record { F-resp-≈ = Function.id }

    module _ (T : Category.Signature 𝒯) where

      private
        category : Category.Signature 𝒮
        category = Signatures.category T

      H-is-functor : Morphism.IsFunctor eq eqₜ category T H
      H-is-functor = record
        { F-resp-id = refl
        ; F-resp-∘ = refl
        }

      functor : Morphism.Functor′ eqₜ category T
      functor = record
        { morphism = H
        ; isHomomorphism = H-is-homomorphism
        ; isFunctor = H-is-functor
        }

      is-category : (Category.Structure eqₜ T) → Category.Structure eq category
      is-category is = Category.Transfer.structure is functor

    module _
      {T : Category.Signature 𝒯} (C : Cartesian.Signature T)
      {T-is-category : Category.Structure eqₜ T}
      (C-is-cartesian : Cartesian.Structure T-is-category C)
      (let module C = Cartesian.Signature C)
      ⦃ terminal : Terminal (𝒮 .Ob) ⦄ ⦃ products : BinaryProducts (𝒮 .Ob) ⦄
      (tH : Iso T ⊤ (H.₀ ⊤))
      (pH : ∀ A B → Iso T (H.₀ A × H.₀ B) (H.₀ (A × B)))
      where

      open Morphisms.Bundles T using (_≅_)
      open Morphisms.Signatures 𝒯 using (_⇔_)
      open Morphisms.Reasoning T-is-category

      ⊤-iso : ⊤ ≅ H.₀ ⊤
      ⊤-iso = record
        { _⇔_ (tH .proj₁)
        ; isIso = tH .proj₂
        }

      ×-iso : ∀ A B → H.₀ A × H.₀ B ≅ H.₀ (A × B)
      ×-iso A B = record
        { _⇔_ (p .proj₁)
        ; isIso = p .proj₂
        } where p = pH A B

      private
        cartesian : Cartesian.Signature (Signatures.category T)
        cartesian = Signatures.cartesian T C
          record { ⊤-iso = tH .proj₁ }
          record { ×-iso = λ A B → pH A B .proj₁ }

        module S where
          open Category.Signature (Signatures.category T) public
          open Cartesian.Signature cartesian public

      H-is-cartesian : Morphism.IsCartesian eq eqₜ cartesian C H
      H-is-cartesian = record
        { ⊤-iso = ⊤-iso
        ; ×-iso = ×-iso
        ; F-resp-! = cancelˡ ⊤-iso.isoˡ
          -- ⊤-iso.to ∘ H.₁ S.!        ≈⟨ refl ⟩
          -- ⊤-iso.to ∘ ⊤-iso.from ∘ ! ≈⟨ cancelˡ ⊤-iso.isoˡ ⟩
          -- !                         ∎
        ; F-resp-⟨⟩ = λ _ _ → cancelˡ ×-iso.isoˡ
          -- ×-iso.to ∘ H.₁ S.⟨ f , g ⟩        ≈⟨ refl ⟩
          -- ×-iso.to ∘ ×-iso.from ∘ ⟨ f , g ⟩ ≈⟨ cancelˡ ×-iso.isoˡ ⟩
          -- ⟨ H.₁ f , H.₁ g ⟩                 ∎
        ; F-resp-π₁ = cancelʳ ×-iso.isoˡ
        ; F-resp-π₂ = cancelʳ ×-iso.isoˡ
        } where module ⊤-iso = _≅_ ⊤-iso
                module ×-iso {A B} = _≅_ (×-iso A B)

      cartesianFunctor : Morphism.Cartesian′ eqₜ cartesian C
      cartesianFunctor = record
        { Morphism.Functor′ (functor T)
        ; isCartesian = H-is-cartesian
        }

      is-cartesian : Cartesian.Structure (is-category T T-is-category) cartesian
      is-cartesian = Cartesian.Transfer.structure C-is-cartesian cartesianFunctor


module Bundles where

  module _
    {o ℓ e}
    (𝒞 : Category.t o ℓ e)
    (let module 𝒞 = Category.t 𝒞)
    {i} {I : Set i} (U : I → 𝒞.𝒬 .Ob)
    where

    category : Category.t i ℓ e
    category = record
      { 𝒬 = 𝒬 𝒞.𝒬 U
      ; category = Signatures.category 𝒞.𝒬 U 𝒞.category
      ; isCategory = Structures.is-category 𝒞.𝒬 U 𝒞.category 𝒞.isCategory
      }

  module _
    {o ℓ e}
    (𝒞 : Cartesian.t o ℓ e)
    (let module 𝒞 = Cartesian.t 𝒞)
    {i} {I : Set i} (U : I → 𝒞.𝒬 .Ob)
    ⦃ terminal : Terminal (𝒮 𝒞.𝒬 U .Ob) ⦄ ⦃ products : BinaryProducts (𝒮 𝒞.𝒬 U .Ob) ⦄
    (let module H = Morphism.t (H 𝒞.𝒬 U))
    (tH : Iso 𝒞.category ⊤ (H.₀ ⊤))
    (pH : ∀ A B → Iso 𝒞.category (H.₀ A × H.₀ B) (H.₀ (A × B)))
    where

    private
      cat : Category.t i ℓ e
      cat = category (record { Cartesian.t 𝒞 }) U

    cartesian : Cartesian.t i ℓ e
    cartesian = record
      { Category.t cat
      ; cartesian = Signatures.cartesian 𝒞.𝒬 U 𝒞.category 𝒞.cartesian
          record { ⊤-iso = tH .proj₁ }
          record { ×-iso = λ A B → pH A B .proj₁ }
      ; isCartesian = Structures.is-cartesian 𝒞.𝒬 U 𝒞.cartesian 𝒞.isCartesian tH pH
      }
