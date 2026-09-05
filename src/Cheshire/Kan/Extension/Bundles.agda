{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Extension.Bundles where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Homomorphism renaming (Homomorphism to t)
import Cheshire.Natural as Natural
import Cheshire.Kan.Extension.Signatures as Signatures
import Cheshire.Kan.Extension.Structures as Structures

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

  record Lan
    (F : Homomorphism.Functor A.eq B.eq A.category B.category)
    (X : Homomorphism.Functor A.eq C.eq A.category C.category)
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    private
      module F = Homomorphism.Functor F
      module X = Homomorphism.Functor X

    field
      signature : Signatures.Lan F.morphism X.morphism
      structure : IsLan C.category C.eq signature

    open Signatures.Lan signature public
    open IsLan structure public


  record Ran
    (F : Homomorphism.Functor A.eq B.eq A.category B.category)
    (X : Homomorphism.Functor A.eq C.eq A.category C.category)
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″ ⊔ e″) where
    no-eta-equality
    private
      module F = Homomorphism.Functor F
      module X = Homomorphism.Functor X

    field
      signature : Signatures.Ran F.morphism X.morphism
      structure : IsRan C.category C.eq signature

    open Signatures.Ran signature public
    open IsRan structure public
