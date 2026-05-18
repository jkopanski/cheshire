{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Traced.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Monoidal.Signature as Monoidal renaming (Monoidal to t)
import Cheshire.Monoidal.Braided.Signature as Braided renaming (Braided to t)

private
  variable
    o ℓ : 𝕃.t

-- nlab defines Tracedₗ, Tracedᵣ and /planar/ traced (and spherical?).
-- agda-categories instead puts symmetric as a requirement (making it
-- spherical? planar?).  I'm going to follow agda-categories here.
record Traced
  {𝒬 : Quiver o ℓ}
  {𝒞 : Category.t 𝒬}
  (ℳ : Monoidal.t 𝒞)
    : Set (𝕃.levelOfTerm ℳ) where
  no-eta-equality
  open Category.t 𝒞
  open Monoidal.t ℳ

  field
    trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
