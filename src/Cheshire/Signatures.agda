{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Signatures
  {o ℓ} (𝒬 : Quiver o ℓ)
  where

open Quiver 𝒬

open import Cheshire.Object.Signatures Ob

private
  variable
    A B C D W X Y Z : Ob
    f g h : X ⇒ Y

record Category : Set (𝕃.suc (o ⊔ ℓ)) where
  no-eta-equality
  infixr 9 _∘_
  field
    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

record Monoidal : Set (𝕃.suc (o ⊔ ℓ)) where
  no-eta-equality
  infixr 9 _∘_
  infixr 10 _⊗₀_ _⊗₁_
  field
    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

    unit : Ob
    -- implement with this?
    -- ⊗  : Bifunctor C C C

    _⊗₀_ : Ob → Ob → Ob
    _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W

  category : Category
  category = record { id = id; _∘_ = _∘_ }

record Cartesian : Set (𝕃.suc (o ⊔ ℓ)) where
  no-eta-equality
  infixr 9 _∘_
  field
    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

    terminal : Terminal
    products : BinaryProducts

  private instance
    _ = terminal; _ = products
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

  category : Category
  category = record { id = id; _∘_ = _∘_ }

  monoidal : Monoidal
  monoidal = record
    { Category category
    ; unit = terminal .Terminal.⊤
    ; _⊗₀_ = _×_
    ; _⊗₁_ = _⁂_
    }
