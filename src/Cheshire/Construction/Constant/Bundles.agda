{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Constant.Bundles where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product as Product
import Cheshire.Instance.One as One

open import Cheshire.Construction.Constant.Signatures
open import Cheshire.Construction.Constant.Structures
open Morphism using (Homomorphism; Functor; IsHomomorphism; IsFunctor)
open Product using (_×ₑ_)

private
  variable
    o ℓ e e′ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ

constant-Homomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒯 → 𝒯 .Ob → Homomorphism 𝒮 𝒯 eqₛ eqₜ
constant-Homomorphism T t = record
  { morphism = constant T t
  ; isHomomorphism = constant-isHomomorphism T t
  }

constant-Functor :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  (S : Category.Signature 𝒮) → {T : Category.Signature 𝒯} →
  (isT : Category.Structure eqₜ T) →
  𝒯 .Ob → Functor eqₛ eqₜ S T
constant-Functor S {T} isT t = record
  { morphism = constant T t
  ; isFunctor = constant-isFunctor S isT t
  ; isHomomorphism = constant-isHomomorphism T t
  }

constant!-Homomorphism :
  ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒯 → 𝒯 .Ob → Homomorphism One.𝒬0 𝒯 (One.eq {e = e′}) eqₜ
constant!-Homomorphism T t = record
  { morphism = constant! T t
  ; isHomomorphism = constant-isHomomorphism T t
  }

constant!-Functor :
  ⦃ eqₜ : Equivalence 𝒯 e ⦄ →
  (S : Category.Signature 𝒮) →
  {T : Category.Signature 𝒯} (isT : Category.Structure eqₜ T) →
  𝒯 .Ob → Functor (One.eq {e = e′}) eqₜ One.category T
constant!-Functor S {T} isT t = record
  { morphism = constant! T t
  ; isFunctor = constant-isFunctor One.category isT t
  ; isHomomorphism = constant-isHomomorphism T t
  }

constantˡ-Homomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒮 → 𝒮 .Ob → Homomorphism 𝒯 (Product.𝒬 𝒮 𝒯) eqₜ (eqₛ ×ₑ eqₜ)
constantˡ-Homomorphism S s = record
  { morphism = constantˡ S s
  ; isHomomorphism = Product.※-isHomomorphism
      (constant-isHomomorphism S s)
      Morphism.id-isHomomorphism
  }

constantˡ-Functor :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  (T : Category.Signature 𝒯) →
  {S : Category.Signature 𝒮} (isS : Category.Structure eqₛ S) →
  𝒮 .Ob → Functor eqₜ (eqₛ ×ₑ eqₜ) T (Product.Category S T)
constantˡ-Functor T {S} isS s = record
  { morphism = constantˡ S s
  ; isFunctor = Product.※-isFunctor
      (constant-isFunctor T isS s)
      (Morphism.id-isFunctor T)
  ; isHomomorphism = Homomorphism.isHomomorphism (constantˡ-Homomorphism S s)
  }

constantʳ-Homomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒮 → 𝒮 .Ob → Homomorphism 𝒯 (Product.𝒬 𝒯 𝒮) eqₜ (eqₜ ×ₑ eqₛ)
constantʳ-Homomorphism S s = record
  { morphism = constantʳ S s
  ; isHomomorphism = Product.※-isHomomorphism
      Morphism.id-isHomomorphism
      (constant-isHomomorphism S s)
  }

constantʳ-Functor :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  (T : Category.Signature 𝒯) →
  {S : Category.Signature 𝒮} (isS : Category.Structure eqₛ S) →
  𝒮 .Ob → Functor eqₜ (eqₜ ×ₑ eqₛ) T (Product.Category T S)
constantʳ-Functor T {S} isS s = record
  { morphism = constantʳ S s
  ; isFunctor = Product.※-isFunctor
      (Morphism.id-isFunctor T)
      (constant-isFunctor T isS s)
  ; isHomomorphism = Homomorphism.isHomomorphism (constantʳ-Homomorphism S s)
  }

