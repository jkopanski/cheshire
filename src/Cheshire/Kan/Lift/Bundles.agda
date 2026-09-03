{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Lift.Bundles where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Homomorphism renaming (Homomorphism to t)
import Cheshire.Natural as Natural
import Cheshire.Kan.Lift.Signatures as Signatures
import Cheshire.Kan.Lift.Structures as Structures

open Structures

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : 𝕃.t

module _
  {A : Category.t o  ℓ  e} {B : Category.t o′ ℓ′ e′} {C : Category.t o″ ℓ″ e″}
  where

  private
    module A = Category.t A
    module B = Category.t B
    module C = Category.t C

  record Lift
    (F : Homomorphism.Functor B.eq C.eq B.category C.category)
    (X : Homomorphism.Functor A.eq C.eq A.category C.category)
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    private
      module F = Homomorphism.Functor F
      module X = Homomorphism.Functor X

    field
      signature : Signatures.Lift F.morphism X.morphism
      structure : IsLift B.category C.category B.eq C.eq signature

    open Signatures.Lift signature public
    open IsLift structure public


  record Rift
    (F : Homomorphism.Functor B.eq C.eq B.category C.category)
    (X : Homomorphism.Functor A.eq C.eq A.category C.category)
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    private
      module F = Homomorphism.Functor F
      module X = Homomorphism.Functor X

    field
      signature : Signatures.Rift F.morphism X.morphism
      structure : IsRift B.category C.category B.eq C.eq signature

    open Signatures.Rift signature public
    open IsRift structure public
