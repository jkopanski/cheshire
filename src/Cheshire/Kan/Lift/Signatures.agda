{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Lift.Signatures where

import Cheshire.Homomorphism.Signatures as Homomorphism renaming (Morphism to t)
import Cheshire.Natural.Signatures as Natural

open Homomorphism using (_∘_)

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : 𝕃.t

-- nlab says:
-- Kan lift is the best approximation to lifting a morphism X : A → C
-- through a morphism F : B → C to a morphism Rift .R : A → B
-- It also names the unique natural transformaion ζ. But In order to
-- distinguish names between Lift and Rift I took the naming from Kan
-- extionsions.
module _
  {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″}
  (F : Homomorphism.t B C) (X : Homomorphism.t A C)
  where

  record Lift : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″) where
    no-eta-equality
    field
      L : Homomorphism.t A B
      η : Natural.Transformation X (F ∘ L)
      σ : (M : Homomorphism.t A B) → (α : Natural.Transformation X (F ∘ M)) → Natural.Transformation L M

    module L = Homomorphism.t L
    module η = Natural.Transformation η


  record Rift : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″) where
    no-eta-equality
    field
      R : Homomorphism.t A B
      ε : Natural.Transformation (F ∘ R) X
      δ : (M : Homomorphism.t A B) → (α : Natural.Transformation (F ∘ M) X) → Natural.Transformation M R

    module R = Homomorphism.t R
    module ε = Natural.Transformation ε
