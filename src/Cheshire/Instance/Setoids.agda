{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Setoids (ℓ : 𝕃.t) where

open import Relation.Binary.Bundles using (Setoid)
import Data.Unit.Polymorphic.Properties as 𝟙ₛ
import Function.Construct.Composition as Comp
import Function.Construct.Constant as Const
import Function.Construct.Identity as Id
import Function.Relation.Binary.Setoid.Equality as SetoidEq renaming (_≈_ to _⟨≗⟩_)

module ×ₛ where
  open import Data.Product.Function.NonDependent.Setoid public
  open import Data.Product.Relation.Binary.Pointwise.NonDependent public

module ⊎ₛ where
  open import Data.Sum.Relation.Binary.Pointwise public

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Object.Signatures as Object

open ×ₛ using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)

𝒬 : Quiver (𝕃.suc ℓ) ℓ
𝒬 = mk⇒ {Ob = Setoid ℓ ℓ} Func.t

instance
  eq : Equivalence 𝒬 ℓ
  eq = record
    { _≈_ = λ {A} {B} f g →
      let open SetoidEq A B
      in f ⟨≗⟩ g
    ; equiv = λ {A} {B} → SetoidEq.isEquivalence A B
    }

open Object (𝒬 .Ob)

instance
  terminal : Terminal
  terminal = record
    { ⊤ = record { Carrier = 𝟙.t; _≈_ = λ _ _ → 𝟙.t } }

  products : BinaryProducts
  products = record { _×_ = ×ₛ.×-setoid }

  coproducts : BinaryCoproducts
  coproducts = record {_⊎_ = ⊎ₛ.⊎-setoid }

category : Category.Signature 𝒬
category = record
  { id = λ {A} → Id.function A
  ; _∘_ = Function.flip Comp.function
  }

is-category : Category.Structure eq category
is-category = record
  { assoc     = λ {A} {_} {_} {D} x → let module D = Setoid.t D in D.refl
  ; identityˡ = λ {f = f} → refl {x = f}
  ; identityʳ = λ {f = f} → refl {x = f}
  ; ∘-resp-≈  = λ {C = C} {f = f} {h} {g} {i} f≈h g≈i → begin
      f ∘ g ≈⟨ f≈h ⊙ Func.t.to g ⟩
      h ∘ g ≈⟨ Func.t.cong h ⊙ g≈i ⟩
      h ∘ i ∎
  } where open EdgeReasoning
          open Category.Signature category

cartesian : Cartesian.Signature category
cartesian = record
  { terminal = terminal
  ; ! = λ {A} → Const.function A ⊤ 𝟙.tt
  ; products = products
  ; π₁ = proj₁ₛ
  ; π₂ = proj₂ₛ
  ; ⟨_,_⟩ = <_,_>ₛ
  }

is-cartesian : Cartesian.Structure is-category cartesian
is-cartesian = record
  { !-unique = λ _ _ → 𝟙.tt
  ; project₁ = λ {h = h} → refl {x = h}
  ; project₂ = λ {i = i} → refl {x = i}
  ; unique   = λ {A B C} p₁ p₂ x →
      let module A = Setoid.t A
          module B = Setoid.t B
      in A.sym (p₁ x) , B.sym (p₂ x)
      -- ×.< sym p₁ , sym p₂ >
  }

Setoids : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
Setoids = record
  { 𝒬 = 𝒬
  ; category = category
  ; cartesian = cartesian
  ; isCategory = is-category
  ; isCartesian = is-cartesian
  }
