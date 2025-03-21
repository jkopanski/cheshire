{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Setoids (o ℓ : 𝕃.t) where

import Function.Bundles as Func renaming (Func to t)

open import Relation.Binary.Bundles using (Setoid)
import Function.Construct.Composition as Comp
import Function.Construct.Identity as Id
import Function.Relation.Binary.Setoid.Equality as SetoidEq renaming (_≈_ to _⟨≗⟩_)

import Cheshire.Signatures as Sig

𝒬 : Quiver (𝕃.suc (o ⊔ ℓ)) (o ⊔ ℓ)
𝒬 = mk⇒ {Ob = Setoid o ℓ} Func.t

instance
  eq : Equivalence 𝒬 (o ⊔ ℓ)
  eq = record
    { _≈_ = λ {A} {B} f g →
      let open SetoidEq A B
      in f ⟨≗⟩ g
    ; equiv = λ {A} {B} → SetoidEq.isEquivalence A B
    }

Setoids : Sig.Category 𝒬
Setoids = record
  { id = λ {A} → Id.function A
  ; _∘_ = flip Comp.function
  }

