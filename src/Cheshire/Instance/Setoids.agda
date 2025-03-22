{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Setoids (o ℓ : 𝕃.t) where

import Function.Bundles as Func renaming (Func to t)

open import Relation.Binary.Bundles using (Setoid)
import Data.Unit.Polymorphic.Properties as 𝟙ₛ
import Function.Construct.Composition as Comp
import Function.Construct.Constant as Const
import Function.Construct.Identity as Id
import Function.Relation.Binary.Setoid.Equality as SetoidEq renaming (_≈_ to _⟨≗⟩_)

module ×ₛ where
  open import Data.Product.Function.NonDependent.Setoid public
  open import Data.Product.Relation.Binary.Pointwise.NonDependent public

module +ₛ where
  open import Data.Sum.Relation.Binary.Pointwise public

import Cheshire.Signatures as Sig
import Cheshire.Object.Signatures as Object

𝒬 : Quiver (𝕃.suc (o ⊔ ℓ)) (o ⊔ ℓ)
𝒬 = mk⇒ {Ob = Setoid o (o ⊔ ℓ)} Func.t

instance
  eq : Equivalence 𝒬 (o ⊔ ℓ)
  eq = record
    { _≈_ = λ {A} {B} f g →
      let open SetoidEq A B
      in f ⟨≗⟩ g
    ; equiv = λ {A} {B} → SetoidEq.isEquivalence A B
    }

open Object (𝒬 .Ob)

instance
  terminal : Terminal
  terminal = λ where
    .⊤ → record { Carrier = 𝟙.t; _≈_ = λ _ _ → 𝟙.t }

  products : BinaryProducts
  products = record { _×_ = ×ₛ.×-setoid }

  coproducts : BinaryCoproducts
  coproducts = record {_+_ = +ₛ.⊎-setoid }

Setoids : Sig.Cartesian 𝒬
Setoids = record
  { id = λ {A} → Id.function A
  ; _∘_ = flip Comp.function
  ; terminal = terminal
  ; ! = λ {A} → Const.function A ⊤ 𝟙.tt
  ; products = products
  ; π₁ = ×ₛ.proj₁ₛ
  ; π₂ = ×ₛ.proj₂ₛ
  ; ⟨_,_⟩ = ×ₛ.<_,_>ₛ
  }

