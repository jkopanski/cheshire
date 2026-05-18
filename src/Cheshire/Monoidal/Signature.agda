{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Monoidal.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Bifunctor.Signature as Bifunctor renaming (Bifunctor to t)

private
  variable
    o ℓ : 𝕃.t
    𝒬 : Quiver o ℓ


record Monoidal (𝒞 : Category.t 𝒬) : Set (𝕃.levelOfTerm 𝒞) where
  no-eta-equality
  open Category.t 𝒞

  infixr 10 _⊗₀_ _⊗₁_

  field
    unit : 𝒬 .Ob
    ⊗  : Bifunctor.t 𝒬 𝒬 𝒬

  module F = Bifunctor.t ⊗
  module ⊗ = Morphism.t F.H

  _⊗₀_ : 𝒬 .Ob → 𝒬 .Ob → 𝒬 .Ob
  _⊗₀_ = ×.curry′ F.₀

  _⊗₁_ : ∀ {W X Y Z : 𝒬 .Ob} → X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  _⊗₁_ = ×.curry F.₁

  _⊗- : 𝒬 .Ob → Morphism.t 𝒬 𝒬
  X ⊗- = F.appˡ X

  -⊗_ : 𝒬 .Ob → Morphism.t 𝒬 𝒬
  -⊗ X = F.appʳ X
