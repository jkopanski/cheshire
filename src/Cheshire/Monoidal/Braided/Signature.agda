{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Braided.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Monoidal.Signature as Monoidal renaming (Monoidal to t)
import Cheshire.Bifunctor.Signature as Bifunctor renaming (Bifunctor to t)
import Cheshire.Morphism.Signatures as Morphisms
import Cheshire.Natural.Signatures as Natural

private
  variable
    o ℓ : 𝕃.t


record Braided {𝒬 : Quiver o ℓ} {𝒞 : Category.t 𝒬} (ℳ : Monoidal.t 𝒞) : Set (𝕃.levelOfTerm ℳ) where
  no-eta-equality
  open Morphisms 𝒬
  open Category.t 𝒞
  open Monoidal.t ℳ

  module F⁻¹ = Bifunctor.t (Bifunctor.t.flip ⊗)

  field
    braiding : Natural.Isomorphism F.H F⁻¹.H

  module braiding = Natural.Isomorphism braiding

  -- Shorthands
  σ⇒ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  σ⇒ {X} {Y} = braiding.⇒.η (X , Y)

  σ⇐ : ∀ {X Y} → Y ⊗₀ X ⇒ X ⊗₀ Y
  σ⇐ {X} {Y} = braiding.⇐.η (X , Y)

  B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  B {X} {Y} = braiding.⇒.η (X , Y)

  braided-iso : ∀ {X Y} → X ⊗₀ Y ⇔ Y ⊗₀ X
  braided-iso = record
    { from = B
    ; to   = B
    }

  module braided-iso {X Y} = _⇔_ (braided-iso {X} {Y})

