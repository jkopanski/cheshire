{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Extension.Signatures where

import Cheshire.Homomorphism.Signatures as Homomorphism renaming (Morphism to t)
import Cheshire.Natural.Signatures as Natural

open Homomorphism using (_∘_)

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : 𝕃.t

-- ncat says:                agda-cat says:
-- p : Homomorphism A B      ≈ F
-- F : Homomorphism A C      ≈ X
-- LanF : Homomorphism B C  ≈ Lan .L

-- The left Kan extension LanF=LanₚF of F along p is a functor LanF
-- equipped with a natural transformation η F : F ⇒ p *LanF. With the
-- property that every other natural transformation F ⇒ p *G factors
-- uniquely through η F.

module _
  {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″}
  (F : Homomorphism.t A B) (X : Homomorphism.t A C)
  where

  record Lan : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″) where
    no-eta-equality
    field
      L : Homomorphism.t B C
      η : Natural.Transformation X (L ∘ F)
      σ : (M : Homomorphism.t B C) → (α : Natural.Transformation X (M ∘ F)) → Natural.Transformation L M

    module L = Homomorphism.t L
    module η = Natural.Transformation η


  record Ran : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″) where
    no-eta-equality
    field
      R : Homomorphism.t B C
      ε : Natural.Transformation (R ∘ F) X
      δ : (M : Homomorphism.t B C) → (α : Natural.Transformation (M ∘ F) X) → Natural.Transformation M R

    module R = Homomorphism.t R
    module ε = Natural.Transformation ε
