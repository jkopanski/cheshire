{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.CounitalCopy.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Monoidal.Signature as Monoidal renaming (Monoidal to t)

private
  variable
    o ℓ : 𝕃.t


record CounitalCopy {𝒬 : Quiver o ℓ} {𝒞 : Category.t 𝒬} (ℳ : Monoidal.t 𝒞) : Set (𝕃.levelOfTerm ℳ) where
  no-eta-equality
  open Category.t 𝒞
  open Monoidal.t ℳ

  field
    Δ : ∀ {X} → X ⇒ X ⊗₀ X
    δ : ∀ {X} → X ⇒ unit
