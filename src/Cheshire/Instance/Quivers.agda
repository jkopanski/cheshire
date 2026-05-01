{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Quivers (o ℓ : 𝕃.t) where

import Cheshire.Category.Signature as Signature renaming (Category to t)
import Cheshire.Category.Structure as Structure renaming (IsCategory to t)
import Cheshire.Category.Bundle as Bundle renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)

private
  variable
    e : 𝕃.t

𝒬 : ∀ o ℓ → Quiver (𝕃.suc (o ⊔ ℓ)) (o ⊔ ℓ)
𝒬 o ℓ = mk⇒ {Ob = Quiver o ℓ} Morphism.t

instance
  eq : Equivalence (𝒬 o ℓ) e
  eq = record
    { _≈_ = {!!}
    ; equiv = record
      { refl = {!!}
      ; trans = {!!}
      ; sym = {!!}
      }
    }


category : Signature.t (𝒬 o ℓ)
category = record
  { id = Morphism.mkM Function.id Function.id
  ; _∘_ = Morphism._∘_
  }

is-category : Structure.t (eq {e}) category
is-category = {!!}
