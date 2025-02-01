{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.One where

module _ {o ℓ : 𝕃.t} where

  𝒬 : Quiver o ℓ
  𝒬 = mk⇒ {Ob = 𝟙.t} λ _ _ → 𝟙.t

  instance
    eq : Equivalence 𝒬 ℓ
    eq = record
      { _≈_ = λ _ _ → 𝟙.t
      ; equiv = record
        { refl = λ {_} → 𝟙.tt
        ; trans = λ _ _ → 𝟙.tt
        ; sym = λ _ → 𝟙.tt
        }
      }

𝒬0 : Quiver 𝕃.0ℓ 𝕃.0ℓ
𝒬0 = -- mk⇒ {Ob = 𝟙.t} λ _ _ → 𝟙.t
  𝒬 {𝕃.0ℓ} {𝕃.0ℓ}

