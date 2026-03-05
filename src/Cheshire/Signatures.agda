{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Signatures where

import Cheshire.Object.Signatures as Object

open import Cheshire.Category.Signature public

module _ {o ℓ} (𝒬 : Quiver o ℓ) where
  open Quiver 𝒬
  open Object (𝒬 .Ob)

  private
    variable
      A B C D W X Y Z : 𝒬 .Ob
      f g h : X ⇒ Y

  record Monoidal : Set (𝕃.suc (o ⊔ ℓ)) where
    no-eta-equality
    infixr 9 _∘_
    infixr 10 _⊗₀_ _⊗₁_
    field
      id : ∀ {A} → A ⇒ A
      _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

      unit : 𝒬 .Ob
      -- implement with this?
      -- ⊗  : Bifunctor C C C

      _⊗₀_ : 𝒬 .Ob → 𝒬 .Ob → 𝒬 .Ob
      _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W

    category : Category 𝒬
    category = record { id = id; _∘_ = _∘_ }

  record Cartesian : Set (𝕃.suc (o ⊔ ℓ)) where
    no-eta-equality
    infixr 9 _∘_
    field
      id : ∀ {A} → A ⇒ A
      _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

      ⦃ terminal ⦄ : Terminal
      ⦃ products ⦄ : BinaryProducts

    field
      ! : ∀ {A} → A ⇒ ⊤

    infix 11 ⟨_,_⟩
    field
      π₁    : ∀ {A B} → A × B ⇒ A
      π₂    : ∀ {A B} → A × B ⇒ B
      ⟨_,_⟩ : ∀ {A B C} → C ⇒ A → C ⇒ B → C ⇒ A × B

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

    category : Category 𝒬
    category = record { id = id; _∘_ = _∘_ }

    monoidal : Monoidal
    monoidal = record
      { Category category
      ; unit = ⊤
      ; _⊗₀_ = _×_
      ; _⊗₁_ = _⁂_
      }
