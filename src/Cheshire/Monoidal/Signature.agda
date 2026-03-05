{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)

private
  variable
    o ℓ : 𝕃.t

record Monoidal (𝒬 : Quiver o ℓ) : Set (𝕃.suc (o ⊔ ℓ)) where
  no-eta-equality
  open Quiver 𝒬

  infixr 9 _∘_
  infixr 10 _⊗₀_ _⊗₁_

  field
    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

    unit : 𝒬 .Ob
    -- implement with this?
    -- ⊗  : Bifunctor C C C

    _⊗₀_ : 𝒬 .Ob → 𝒬 .Ob → 𝒬 .Ob
    _⊗₁_ : ∀ {W X Y Z : 𝒬 .Ob} → X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W

  category : Category.t 𝒬
  category = record { id = id; _∘_ = _∘_ }
