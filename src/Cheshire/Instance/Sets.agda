{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Sets (o : 𝕃.t) where

import Function
import Data.Product as ×
import Data.Sum as ⊎

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Object.Signatures as Object

𝒬 : Quiver (𝕃.suc o) o
𝒬 = mk⇒ λ c d → c → d
open Object (𝒬 .Ob)

instance
  eq : Equivalence 𝒬 o
  eq = record
    { _≈_ = Rel₂._≗_
    ; equiv = record
      { refl = λ _ → Rel₂.refl
      ; trans = λ eq₁ eq₂ x → Rel₂.trans (eq₁ x) (eq₂ x)
      ; sym = λ eq x → Rel₂.sym (eq x)
      }
    }

  terminal : Terminal
  terminal = record { ⊤ = 𝟙.t }

  initial : Initial
  initial = record { ⊥ = 𝟘.t }

  products : BinaryProducts
  products = record { _×_ = ×._×_ }

  coproducts : BinaryCoproducts
  coproducts = record { _⊎_ = ⊎._⊎_ }

category : Category.Signature 𝒬
category = record
  { id = Function.id
  ; _∘_ = Function._∘′_
  }

Sets : Cartesian.Signature 𝒬
Sets = record
  { category = category
  ; terminal = terminal
  ; ! = Function.const 𝟙.tt
  ; products = products
  ; π₁ = ×.proj₁
  ; π₂ = ×.proj₂
  ; ⟨_,_⟩ = ×.<_,_>
  }
