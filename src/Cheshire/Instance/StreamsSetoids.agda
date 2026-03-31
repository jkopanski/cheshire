{-# OPTIONS --safe --guardedness #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.StreamsSetoids (o : 𝕃.t) where

import Codata.Guarded.Stream as Stream renaming (Stream to t)
import Codata.Guarded.Stream.Properties as Streamₚ
import Codata.Guarded.Stream.Relation.Binary.Pointwise as Pointwise
import Relation.Binary.Indexed.Homogeneous.Bundles as IndexedSetoid renaming (IndexedSetoid to t)
import Relation.Binary.Indexed.Homogeneous.Construct.At as At

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Instance.Setoids o as Setoids
import Cheshire.Construction.Sub.Object as SubObject

open ℕ using (_<_; _≤_; _+_)
open Stream using (_∷_; _[_])
open At using (_atₛ_)
open IndexedSetoid.t

-- Is that accurate?
-- Initially I've tried to do it as Sub category of Sets.  However
-- that gives me equality (as lifted by Morhpism.t 𝒬 Sets.𝒬) that is
-- propositional equality on streams.  I think this is useless, as
-- only definotially equal stream would be, well equal.  That is 2
-- streams that produce the same values might not be equal if they are
-- defined differently.

-- So I need to use Pointwise equality, that means I need a setoids.
-- But I don't see how I could define Streaming functions as sub
-- category of Setoids?

module Sub = SubObject Setoids.𝒬

-- TODO: to stdlib?
indexedSetoid : IndexedSetoid.t (Set o) o o
indexedSetoid = record
  { Carrierᵢ = Stream.t
  ; _≈ᵢ_ = Pointwise._≈_
  ; isEquivalenceᵢ = record
    { reflᵢ  = Pointwise.refl
    ; symᵢ   = Pointwise.sym
    ; transᵢ = Pointwise.trans
    }
  }

U : Set o → Setoid.t o o
U = At.setoid indexedSetoid

𝒬 : Quiver (𝕃.suc o) o
𝒬 = Sub.𝒬 U

H : Morphism.t 𝒬 Setoids.𝒬
H = Sub.Signatures.H

private
  variable
    A B C : 𝒬 .Ob
    m n : ℕ.t
    s t : Carrierᵢ indexedSetoid A

instance
  eq : Equivalence 𝒬 o
  eq = Morphism.equivalence Setoids.eq H

category : Category.Signature 𝒬
category = Sub.Signatures.category Setoids.category

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
  { from = record
    { to = Stream.repeat
    ; cong = λ _ → Pointwise.tabulate⁺ (λ _ → ≡-refl)
    }
  ; to = record
    { to = const 𝟙.tt
    ; cong = λ _ → 𝟙.tt
    }
  }

productsH : Morphism.BinaryProducts H
productsH .Morphism.BinaryProducts.×-iso = λ _ _ → record
  { from = record
    { to = ×.uncurry′ (Stream.zipWith _,_)
    ; cong = ×.uncurry′ (Streamₚ.cong-zipWith _,_)
    }
  ; to = record
    { to = λ abs → Stream.map proj₁ abs , Stream.map proj₂ abs
    ; cong = λ eq → Streamₚ.cong-map proj₁ eq , Streamₚ.cong-map proj₂ eq
    }
  }

map : (A → B) → A ⇒ B
map f = record
  { to = Stream.map f
  ; cong = Streamₚ.cong-map f
  }

delayˢ : A → A ⇒ A
delayˢ a = record
  { to = a ∷_
  ; cong = λ x≈y → ≡-refl Pointwise.∷ x≈y
  }

buffer : Vec.t A n → A ⇒ A
buffer Vec.[] = id
buffer (v Vec.∷ vs) = delayˢ v ∘ buffer vs

infixr 5 _◃_
_◃_ : Vec.t A n → A ⇒ A
_◃_ = buffer
