{-# OPTIONS --safe --guardedness #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Streams (o : 𝕃.t) where

import Codata.Guarded.Stream as Stream renaming (Stream to t)
import Codata.Guarded.Stream.Properties as Streamₚ
import Codata.Guarded.Stream.Relation.Binary.Pointwise as Pointwise

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Instance.Sets o as Sets
import Cheshire.Construction.Sub.Object as SubObject

open ℕ using (_<_; _≤_; _+_)
open Stream using (_[_])
open Pointwise using () renaming (_≈_ to _≈ₛ_)

module Sub = SubObject Sets.𝒬

𝒬 : Quiver (𝕃.suc o) o
𝒬 = Sub.𝒬 Stream.t

H : Morphism.t 𝒬 Sets.𝒬
H = Sub.Signatures.H

private
  variable
    A B C : Set o
    n : ℕ.t

instance
  eq : Equivalence 𝒬 o
  eq = Morphism.equivalence Sets.eq H

category : Category.Signature 𝒬
category = Sub.Signatures.category Sets.category

open Category.Signature category
open Object (𝒬 .Ob)

instance
  terminal : Terminal
  terminal .⊤ = 𝟙.t

  products : BinaryProducts
  products ._×_ = ×._×_

  coproducts : BinaryCoproducts
  coproducts ._⊎_ = ⊎._⊎_

terminalH : Morphism.Terminal H
terminalH .Morphism.Terminal.⊤-iso = record
  { from = Stream.repeat
  ; to = Function.const 𝟙.tt
  }

productsH : Morphism.BinaryProducts H
productsH .Morphism.BinaryProducts.×-iso = λ _ _ → record
  { from = ×.uncurry′ (Stream.zipWith _,_)
  ; to = λ abs → Stream.map proj₁ abs , Stream.map proj₂ abs
  }

cartesian : Cartesian.Signature category
cartesian = Sub.Signatures.cartesian Sets.cartesian terminalH productsH

map : (A → B) → A ⇒ B
map = Stream.map

delayˢ : A → A ⇒ A
delayˢ a = a Stream.∷_

buffer : Vec.t A n → A ⇒ A
buffer v = Vec.toList v Stream.++_

infixr 5 _◃_
_◃_ : Vec.t A n → A ⇒ A
_◃_ = buffer
