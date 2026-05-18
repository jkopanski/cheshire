{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Symmetric.Structure where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal.Signature as Monoidal renaming (Monoidal to t)
import Cheshire.Monoidal.Braided.Signature as Braided renaming (Braided to t)
import Cheshire.Morphism as Morphisms

private
  variable
    o ℓ e : 𝕃.t
    𝒬 : Quiver o ℓ


record IsSymmetric
  {eq : Equivalence 𝒬 e}
  {𝒞 : Category.Signature 𝒬}
  (isCategory : Category.Structure eq 𝒞)
  {ℳ : Monoidal.t 𝒞} (ℬ : Braided.t ℳ)
    : Set (𝕃.levelOfTerm ℬ ⊔ 𝕃.suc e) where
  no-eta-equality
  open Braided.t ℬ hiding (braided-iso)
  open Category.Signature 𝒞
  open Monoidal.t ℳ
  open Morphisms.Signatures 𝒬
  open Morphisms.Structures 𝒞
  open Morphisms.Bundles 𝒞
  private instance _ = eq

  field
    commutative : ∀ {X Y} → B {X} {Y} ∘ B {Y} {X} ≈ id

  braided-isIso : ∀ {X Y} → IsIso (B {X} {Y}) B
  braided-isIso = record
    { isoˡ = commutative
    ; isoʳ = commutative
    }

  braided-iso : ∀ {X Y} → X ⊗₀ Y ≅ Y ⊗₀ X
  braided-iso = record
    { _⇔_ (Braided.t.braided-iso ℬ)
    ; isIso = braided-isIso
    }

