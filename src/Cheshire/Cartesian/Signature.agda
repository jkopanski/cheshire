{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture renaming (module × to P)

module Cheshire.Cartesian.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Monoidal.Signature as Monoidal renaming (Monoidal to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Bifunctor.Signature as Bifunctor renaming (Bifunctor to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism.Signatures as Morphisms
import Cheshire.Natural.Signatures as Natural

import Cheshire.Construction.Bifunctor.Signatures as MkBifunctor
import Cheshire.Construction.Product.Signatures as Product

open MkBifunctor using (bifunctor)

private
  variable
    o ℓ : 𝕃.t
    𝒬 : Quiver o ℓ

record Cartesian (𝒞 : Category.t 𝒬) : Set (𝕃.levelOfTerm 𝒞) where
  no-eta-equality
  open Category.t 𝒞
  open Object (𝒬 .Ob)

  field
    instance
      terminal : Terminal
      products : BinaryProducts

  private
    instance
      _ = terminal; _ = products

  field
    ! : ∀ {A} → A ⇒ ⊤

  infix 11 ⟨_,_⟩
  field
    π₁    : ∀ {A B} → A × B ⇒ A
    π₂    : ∀ {A B} → A × B ⇒ B
    ⟨_,_⟩ : ∀ {A B C} → C ⇒ A → C ⇒ B → C ⇒ A × B

  private
    variable
      A B C D : 𝒬 .Ob

  swap : A × B ⇒ B × A
  swap = ⟨ π₂ , π₁ ⟩

  infixr 8 _⁂_
  _⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
  f ⁂ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  first : A ⇒ B → A × C ⇒ B × C
  -- first f = f ⁂ id
  first f = ⟨ f ∘ π₁ , π₂ ⟩

  second : C ⇒ D → A × C ⇒ A × D
  -- second g = id ⁂ g
  second g = ⟨ π₁ , g ∘ π₂ ⟩

  assocˡ : (A × B) × C ⇒ A × B × C
  assocˡ = ⟨ π₁ ∘ π₁ , first π₂ ⟩

  assocʳ : A × B × C ⇒ (A × B) × C
  assocʳ = ⟨ second π₁ , π₂ ∘ π₂ ⟩

  Δ : ∀ {C} → C ⇒ C × C
  Δ {C} = ⟨ id , id ⟩

  -×- : Bifunctor.t 𝒬 𝒬 𝒬
  -×- = bifunctor 𝒞 𝒞 H
    where H : Morphism.t (Product.𝒬 𝒬 𝒬) 𝒬
          H = record { F₀ = P.uncurry′ _×_; F₁ = P.uncurry′ _⁂_ }

  -×_ : 𝒬 .Ob → Morphism.t 𝒬 𝒬
  -×_ = Bifunctor.t.appʳ -×-

  _×- : 𝒬 .Ob → Morphism.t 𝒬 𝒬
  _×- = Bifunctor.t.appˡ -×-

  open Morphisms 𝒬

  ⊤×A⇔A : ⊤ × A ⇔ A
  ⊤×A⇔A = record
    { from = π₂
    ; to = ⟨ ! , id ⟩
    }

  A×⊤⇔A : A × ⊤ ⇔ A
  A×⊤⇔A = record
    { from = π₁
    ; to = ⟨ id , ! ⟩
    }

  ⊤×- : Natural.Isomorphism (⊤ ×-) Morphism.id
  ⊤×- = record
    { F⇒G = record { η = λ _ → π₂ }
    ; F⇐G = record { η = λ _ → ⟨ ! , id ⟩ }
    ; iso = λ _ → ⊤×A⇔A
    }

  -×⊤ : Natural.Isomorphism (-× ⊤) Morphism.id
  -×⊤ = record
    { F⇒G = record { η = λ _ → π₁ }
    ; F⇐G = record { η = λ _ → ⟨ id , ! ⟩ }
    ; iso = λ _ → A×⊤⇔A
    }

  monoidal : Monoidal.t 𝒞
  monoidal = record
    { unit = ⊤
    ; ⊗ = -×-
    }

  braided : Monoidal.Braided monoidal
  braided = record
    { braiding = record
      { F⇐G = record { η = λ _ → swap }
      ; F⇒G = record { η = λ _ → swap }
      ; iso = λ x → record { from = swap; to = swap }
      }
    }
