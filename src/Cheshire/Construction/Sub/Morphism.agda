{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Construction.Sub.Morphism where

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Prop as Prop
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms

open × using (Σ-syntax)
open Function using (_-⟨_⟩-_)
open Object
open Morphisms.Bundles using (Iso)

private
  variable
    o ℓ ℓ′ e : 𝕃.t

𝒬 : (𝒰 : Quiver o ℓ) → (R : ∀ {A B} → Rel₁.Pred (𝒰 .Hom A B) ℓ′) → Quiver o (ℓ ⊔ ℓ′)
𝒬 𝒰 R = mk⇒ λ X Y → Σ[ f ∈ 𝒰 .Hom X Y ] (R f)

module _
  (𝒯 : Quiver o ℓ)
  (R : ∀ {A B} → Rel₁.Pred (𝒯 .Hom A B) ℓ′)
  where

  𝒮 : Quiver o (ℓ ⊔ ℓ′)
  𝒮 = 𝒬 𝒯 R

  H : Morphism.t 𝒮 𝒯
  H = record
    { F₀ = Function.id
    ; F₁ = ×.proj₁
    }

  private module H = Morphism.t H

  module Signatures {T : Category.Signature 𝒯} (P : Prop.Category R T) where

    open Category.Signature T

    category : Category.Signature 𝒮
    category = record
      { id = id , P.id
      ; _∘_ = λ (g , gᴿ) (f , fᴿ) → g ∘ f , gᴿ P.∘ fᴿ
      } where module P = Prop.Category P

    cartesian :
      {C : Cartesian.Signature T}
      (P : Prop.Cartesian R C) →
      Cartesian.Signature category
    cartesian {C = C} P = record
      { terminal = terminal
      ; ! = ! , P.!
      ; products = products
      ; π₁ = π₁ , P.π₁
      ; π₂ = π₂ , P.π₂
      ; ⟨_,_⟩ = λ (f , fᴿ) (g , gᴿ)  → ⟨ f , g ⟩ , P.⟨ fᴿ , gᴿ ⟩
      } where open Cartesian.Signature C
              module P = Prop.Cartesian P

  module Structures {e} ⦃ eqₜ : Equivalence 𝒯 e ⦄ where

    eq : Equivalence 𝒮 e
    eq = Morphism.equivalence eqₜ H

    H-is-homomorphism : Morphism.IsHomomorphism eq eqₜ H
    H-is-homomorphism = record { F-resp-≈ = Function.id }


    module _ {T : Category.Signature 𝒯} (P : Prop.Category R T) where

      private
        category : Category.Signature 𝒮
        category = Signatures.category P

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
      {T : Category.Signature 𝒯} {C : Cartesian.Signature T}
      (P : Prop.Category R T) (P′ : Prop.Cartesian R C)
      {T-is-category : Category.Structure eqₜ T}
      (C-is-cartesian : Cartesian.Structure T-is-category C)
      where

      open Morphisms.Bundles T using (_≅_)
      open Morphisms.Signatures 𝒯 using (_⇔_)
      open Morphisms.Reasoning T-is-category
      private module T where
        open Category.Signature T public
        open Cartesian.Signature C public
        open Category.Structure T-is-category public

      instance
        terminal : Terminal (𝒮 .Ob)
        terminal = Cartesian.Signature.terminal C

        products : BinaryProducts (𝒮 .Ob)
        products = Cartesian.Signature.products C

      ⊤-iso : ⊤ ≅ H.₀ ⊤
      ⊤-iso = record
        { to = T.id
        ; from = T.id
        ; isIso = record { isoˡ = T.identityˡ; isoʳ = T.identityˡ }
        }

      ×-iso : ∀ A B → H.₀ A × H.₀ B ≅ H.₀ (A × B)
      ×-iso A B = record
        { to = T.id
        ; from = T.id
        ; isIso = record { isoˡ = T.identityˡ; isoʳ = T.identityˡ }
        }

      private
        cartesian : Cartesian.Signature (Signatures.category P)
        cartesian = Signatures.cartesian P P′

      H-is-cartesian : Morphism.IsCartesian eq eqₜ cartesian C H
      H-is-cartesian = record
        { ⊤-iso = ⊤-iso
        ; ×-iso = ×-iso
        ; F-resp-! = T.identityˡ
        ; F-resp-⟨⟩ = λ _ _ → T.identityˡ
        ; F-resp-π₁ = T.identityʳ
        ; F-resp-π₂ = T.identityʳ
        }

      cartesianFunctor : Morphism.Cartesian′ eqₜ cartesian C
      cartesianFunctor = record
        { Morphism.Functor′ (functor P)
        ; isCartesian = H-is-cartesian
        }

      is-cartesian : Cartesian.Structure (is-category P T-is-category) cartesian
      is-cartesian = Cartesian.Transfer.structure C-is-cartesian cartesianFunctor

module Bundles where

  module _
    {o ℓ e}
    (𝒞 : Category.t o ℓ e)
    (let module 𝒞 = Category.t 𝒞)
    {ℓ′} (R : ∀ {A B} → Rel₁.Pred (𝒞.𝒬 .Hom A B) ℓ′)
    (P : Prop.Category R 𝒞.category)
    where

    category : Category.t o (ℓ ⊔ ℓ′) e
    category = record
      { 𝒬 = 𝒬 𝒞.𝒬 R
      ; category = Signatures.category 𝒞.𝒬 R P
      ; isCategory = Structures.is-category 𝒞.𝒬 R P 𝒞.isCategory
      }

  module _
    {o ℓ e}
    (𝒞 : Cartesian.t o ℓ e)
    (let module 𝒞 = Cartesian.t 𝒞)
    {ℓ′} (R : ∀ {A B} → Rel₁.Pred (𝒞.𝒬 .Hom A B) ℓ′)
    (P : Prop.Category R 𝒞.category) (P′ : Prop.Cartesian R 𝒞.cartesian)
    where

    private
      cat : Category.t o (ℓ ⊔ ℓ′) e
      cat = category (record { Cartesian.t 𝒞 }) R P

    cartesian : Cartesian.t o (ℓ ⊔ ℓ′) e
    cartesian = record
      { Category.t cat
      ; cartesian = Signatures.cartesian 𝒞.𝒬 R P P′
      ; isCartesian = Structures.is-cartesian 𝒞.𝒬 R P P′ 𝒞.isCartesian
      }

