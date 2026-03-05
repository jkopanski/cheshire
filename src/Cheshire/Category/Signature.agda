{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Category.Signature where

record Category {o ℓ} (𝒬 : Quiver o ℓ) : Set (𝕃.suc (o ⊔ ℓ)) where
  no-eta-equality
  infixr 9 _∘_
  open Quiver 𝒬
  field
    id : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

infix 10 _[_∘_]
_[_∘_] :
  ∀ {o ℓ} → {𝒬 : Quiver o ℓ} → Category 𝒬 →
  ∀ {A B C} → 𝒬 [ B , C ] → 𝒬 [ A , B ] → 𝒬 [ A , C ]
_[_∘_] = Category._∘_
