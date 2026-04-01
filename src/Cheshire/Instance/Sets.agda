{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Sets (o : 𝕃.t) where

import Function
import Data.Product as ×
import Data.Sum as ⊎

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
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

is-category : Category.Structure o category
is-category = record
  { assoc     = λ _ → ≡-refl
  ; identityˡ = λ _ → ≡-refl
  ; identityʳ = λ _ → ≡-refl
  ; ∘-resp-≈  = λ {h = h} f≈h g≈i x → ≡-trans (f≈h _) (cong h (g≈i x))
  }

cartesian : Cartesian.Signature category
cartesian = record
  { terminal = terminal
  ; ! = Function.const 𝟙.tt
  ; products = products
  ; π₁ = ×.proj₁
  ; π₂ = ×.proj₂
  ; ⟨_,_⟩ = ×.<_,_>
  }

is-cartesian : Cartesian.Structure is-category cartesian
is-cartesian = record
  { !-unique = λ _ _ → ≡-refl
  ; project₁ = λ _ → ≡-refl
  ; project₂ = λ _ → ≡-refl
  ; unique   = λ p₁ p₂ x → ≡-sym $ Rel₂.cong₂ _,_ (p₁ x) (p₂ x)
  }

Sets : Cartesian.t (𝕃.suc o) o o
Sets = record
  { 𝒬 = 𝒬
  ; category = category
  ; cartesian = cartesian
  ; isCategory = is-category
  ; isCartesian = is-cartesian
  }
