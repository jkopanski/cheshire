{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.One where

import Cheshire.Category as Category renaming (IsCategory to Structure)


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

  One : Category.Signature 𝒬
  One = record
    { id = 𝟙.tt
    ; _∘_ = λ _ _ → 𝟙.tt
    }

  IsCategory : Category.Structure e One
  IsCategory = record
    { assoc = 𝟙.tt
    ; identityˡ = 𝟙.tt
    ; identityʳ = 𝟙.tt
    ; ∘-resp-≈ = λ _ _ → 𝟙.tt
    }

𝒬0 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬0 = -- mk⇒ {Ob = 𝟙.t} λ _ _ → 𝟙.t
  𝒬 {𝕃.0ℓ} {𝕃.0ℓ}

One0 : Category.Signature 𝒬0
One0 = One {𝕃.0ℓ} {𝕃.0ℓ}
