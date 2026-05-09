{-# OPTIONS --safe --guardedness #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Streams (o : 𝕃.t) where

import Codata.Guarded.Stream as Stream renaming (Stream to t)
import Codata.Guarded.Stream.Properties as Streamₚ
import Codata.Guarded.Stream.Relation.Binary.Pointwise as Pointwise
import Relation.Binary.Indexed.Homogeneous.Bundles as IndexedSetoid renaming (IndexedSetoid to t)
import Relation.Binary.Indexed.Homogeneous.Construct.At as At

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms
import Cheshire.Instance.Sets o as Sets
import Cheshire.Instance.Setoids o as Setoids renaming (Setoids to t)
import Cheshire.Construction.Sub.Object as Sub

open ℕ using (_<_; _≤_; _+_)
open Function using (_∘₂′_)
open Stream using (_∷_; _[_])
open At using (_atₛ_)
open Morphisms.Bundles Setoids.category using (_≅_; Iso)
open Pointwise
  using (Pointwise; head; tail; module ≈-Reasoning)
  renaming (_≈_ to _≈ₛ_)
open Object
open Morphisms.Structures.IsIso
open IndexedSetoid.t
open ≈-Reasoning

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

------------------------------------------------------------------------
-- Streaming functions category as subcategory of Setoids

U : Sets.𝒬 .Ob → Setoid.t o o
U = At.setoid indexedSetoid

𝒬 : Quiver (𝕃.suc o) o
𝒬 = Sub.𝒬 Setoids.𝒬 U

H : Morphism.t 𝒬 Setoids.𝒬
H = Sub.H Setoids.𝒬 U

private
  module H = Morphism.t H

  variable
    A B C : 𝒬 .Ob
    m n : ℕ.t
    s t : Carrierᵢ indexedSetoid A

instance
  eq : Equivalence 𝒬 o
  eq = Morphism.equivalence Setoids.eq H

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

private module tH = Morphism.Terminal terminalH

terminalH-isIso :
  Morphisms.Structures.IsIso
  Setoids.category
  tH.⊤-iso.from tH.⊤-iso.to
terminalH-isIso .isoˡ _ = 𝟙.tt
terminalH-isIso .isoʳ = go where
  go : (x : Stream.t 𝟙.t) → Stream.repeat 𝟙.tt ≈ₛ x
  go _ .head = ≡-refl
  go x .tail = go (Stream.tail x)

⊤-iso : Iso ⊤ (H.₀ ⊤)
⊤-iso = tH.⊤-iso , terminalH-isIso

productsH : Morphism.BinaryProducts H
productsH .Morphism.BinaryProducts.×-iso _ _ = record
  { from = record
    { to = ×.uncurry′ (Stream.zipWith _,_)
    ; cong = ×.uncurry′ (Streamₚ.cong-zipWith _,_)
    }
  ; to = record
    { to = λ abs → Stream.map proj₁ abs , Stream.map proj₂ abs
    ; cong = λ eq → Streamₚ.cong-map proj₁ eq , Streamₚ.cong-map proj₂ eq
    }
  }

private module pH = Morphism.BinaryProducts productsH

productsH-isIso :
  ∀ {A B} →
  Morphisms.Structures.IsIso
  Setoids.category
  (pH.×-iso.from {A} {B}) pH.×-iso.to
productsH-isIso .isoˡ (sa , sb) =
  ( run
    (Stream.map proj₁ (Stream.zipWith _,_ sa sb) ≈⟨ Streamₚ.map-zipWith proj₁ _,_ sa sb ⟩
    Stream.zipWith Function.const sa sb          ≈⟨ Streamₚ.zipWith-const sa sb ⟩
    sa                                           ∎)
  , run
    (Stream.map proj₂ (Stream.zipWith _,_ sa sb)        ≈⟨ Streamₚ.map-zipWith proj₂ _,_ sa sb ⟩
    Stream.zipWith (Function.flip Function.const) sa sb ≈⟨ Streamₚ.zipWith-flip Function.const sa sb ⟩
    Stream.zipWith Function.const sb sa                 ≈⟨ Streamₚ.zipWith-const sb sa ⟩
    sb                                                  ∎)
  )
productsH-isIso .isoʳ = go where
  go :
    (abs : Stream.t (A × B)) →
    Stream.zipWith _,_ (Stream.map proj₁ abs) (Stream.map proj₂ abs) ≈ₛ abs
  go abs .head = ≡-refl
  go abs .tail = go (Stream.tail abs)

×-iso : ∀ A B → Iso (H.₀ A × H.₀ B) (H.₀ (A × B))
×-iso A B = pH.×-iso A B , productsH-isIso

Streams : Cartesian.t (𝕃.suc o) o o
Streams = Sub.Bundles.cartesian Setoids.t U ⊤-iso ×-iso

------------------------------------------------------------------------
-- Utilities for Streaming functions

open Cartesian.t Streams

map : (A → B) → A ⇒ B
map f = record
  { to = Stream.map f
  ; cong = Streamₚ.cong-map f
  }

delay : A → A ⇒ A
delay a = record
  { to = a ∷_
  ; cong = λ x≈y → ≡-refl Pointwise.∷ x≈y
  }

buffer : Vec.t A n → A ⇒ A
buffer Vec.[] = id
buffer (v Vec.∷ vs) = delay v ∘ buffer vs

infixr 5 _◃_
_◃_ : Vec.t A n → A ⇒ A
_◃_ = buffer
