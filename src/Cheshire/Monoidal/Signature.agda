{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Monoidal.Signature where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Bifunctor.Signature as Bifunctor renaming (Bifunctor to t)
import Cheshire.Morphism.Signatures as Morphisms
import Cheshire.Natural.Signatures as Natural

private
  variable
    o ℓ : 𝕃.t
    𝒬 : Quiver o ℓ
    𝒞 : Category.t 𝒬

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


record Braided {𝒬 : Quiver o ℓ} {𝒞 : Category.t 𝒬} (ℳ : Monoidal 𝒞) : Set (𝕃.levelOfTerm ℳ) where
  no-eta-equality
  open Morphisms 𝒬
  open Category.t 𝒞
  open Monoidal ℳ

  module F⁻¹ = Bifunctor.t (Bifunctor.t.flip ⊗)

  field
    braiding : Natural.Isomorphism F.H F⁻¹.H

  module braiding = Natural.Isomorphism braiding

  B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  B {X} {Y} = braiding.⇒.η (X , Y)

  braided-iso : ∀ {X Y} → X ⊗₀ Y ⇔ Y ⊗₀ X
  braided-iso = record
    { from = B
    ; to   = B
    }

  module braided-iso {X Y} = _⇔_ (braided-iso {X} {Y})


-- nlab defines Tracedₗ, Tracedᵣ and /planar/ traced (and spherical?).
-- agda-categories instead puts symmetric as a requirement (making it
-- spherical? planar?).  I'm going to follow agda-categories here.
record Traced {𝒬 : Quiver o ℓ} {𝒞 : Category.t 𝒬} (ℳ : Monoidal 𝒞) : Set (𝕃.levelOfTerm ℳ) where
  no-eta-equality
  open Category.t 𝒞
  open Monoidal ℳ
  field
    symmetric : Braided ℳ

  open Braided symmetric

  field
    trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
