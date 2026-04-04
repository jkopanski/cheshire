{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.One where

import Cheshire.Category.Signature as Signature renaming (Category to t)
import Cheshire.Category.Structure as Structure renaming (IsCategory to t)
import Cheshire.Category.Bundle as Bundle renaming (Category to t)

module _ {o ℓ : 𝕃.t} where

  private
    variable
      e : 𝕃.t

  𝒬 : Quiver o ℓ
  𝒬 = mk⇒ {Ob = 𝟙.t} λ _ _ → 𝟙.t

  instance
    eq : Equivalence 𝒬 e
    eq = record
      { _≈_ = λ _ _ → 𝟙.t
      ; equiv = record
        { refl = λ {_} → 𝟙.tt
        ; trans = λ _ _ → 𝟙.tt
        ; sym = λ _ → 𝟙.tt
        }
      }

  category : Signature.t 𝒬
  category = record
    { id = 𝟙.tt
    ; _∘_ = λ _ _ → 𝟙.tt
    }

  is-category : ∀ e → Structure.t (eq {e}) category
  is-category _ = record
    { assoc = 𝟙.tt
    ; identityˡ = 𝟙.tt
    ; identityʳ = 𝟙.tt
    ; ∘-resp-≈ = λ _ _ → 𝟙.tt
    }

  One : Bundle.t o ℓ e
  One {e = e} = record
    { 𝒬 = 𝒬
    ; eq = eq
    ; category = category
    ; isCategory = is-category e
    }


𝒬0 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬0 = -- mk⇒ {Ob = 𝟙.t} λ _ _ → 𝟙.t
  𝒬 {𝕃.0ℓ} {𝕃.0ℓ}

category0 : Signature.t 𝒬0
category0 = category {𝕃.0ℓ} {𝕃.0ℓ}

One0 : Bundle.t 𝕃.0ℓ 𝕃.0ℓ 𝕃.0ℓ
One0 = One
