{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Natural.Equivalence
  {o ℓ o′ ℓ′ e}
  {𝒮 : Quiver o ℓ } {𝒯 : Quiver o′ ℓ′}
  (eq : Equivalence 𝒯 e)
  where

import Cheshire.Homomorphism.Signatures as Homomorphism renaming (Morphism to t)
import Cheshire.Natural.Signatures as Natural

module _ {F G : Homomorphism.t 𝒮 𝒯} where

  open Natural.Transformation
  infix 4 _≃_

  _≃_ : Rel₂.Rel (Natural.Transformation F G) (o ⊔ e)
  X ≃ Y = ∀ {x} → eq [ X .η x ≈ Y .η x ]

  ≃-isEquivalence : Rel₂.IsEquivalence _≃_
  ≃-isEquivalence = record
    { refl  = eq .refl
    ; sym   = λ f → eq .sym f
    ; trans = λ f g → eq .trans f g
    }

≃-setoid : (F G : Homomorphism.t 𝒮 𝒯) → Rel₂.Setoid (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (o ⊔ e)
≃-setoid F G = record
  { Carrier = Natural.Transformation F G
  ; _≈_ = _≃_
  ; isEquivalence = ≃-isEquivalence
  }
