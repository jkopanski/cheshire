{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Constant.Bundles where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product as Product
import Cheshire.Instance.One as One renaming (One0 to t)

open import Cheshire.Construction.Constant.Signatures
open import Cheshire.Construction.Constant.Structures
open Morphism using (Homomorphism; Functor; IsHomomorphism; IsFunctor)

private
  variable
    o ℓ e e′ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ

constant-Homomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒯 → 𝒯 .Ob → Homomorphism 𝒮 𝒯
constant-Homomorphism T t = record
  { signature = constant T t
  ; structure = constant-isHomomorphism T t
  }

constant-Functor :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄
  (S : Category.Signature 𝒮) → {T : Category.Signature 𝒯} →
  (isT : Category.Structure e′ T) →
  𝒯 .Ob → Functor ⦃ eqₛ ⦄ ⦃ Category.Structure.eq isT ⦄ S T
constant-Functor S {T} isT t = record
  { signature = constant T t
  ; structure = constant-isFunctor S isT t
  ; isHomomorphism = constant-isHomomorphism T t
  }

constant!-Homomorphism :
  ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒯 → 𝒯 .Ob → Homomorphism One.𝒬0 𝒯 ⦃ One.eq {e = e′} ⦄
constant!-Homomorphism T t = record
  { signature = constant! T t
  ; structure = constant-isHomomorphism T t
  }

constant!-Functor :
  (S : Category.Signature 𝒮) → {T : Category.Signature 𝒯} →
  (isT : Category.Structure e′ T) →
  𝒯 .Ob → Functor ⦃ One.eq {e = e′}⦄ One.t T
constant!-Functor S {T} isT t = record
  { signature = constant! T t
  ; structure = constant-isFunctor One.t isT t
  ; isHomomorphism = constant-isHomomorphism T t
  }

constantˡ-Homomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒮 → 𝒮 .Ob → Homomorphism 𝒯 (Product.𝒬 𝒮 𝒯)
constantˡ-Homomorphism S s = record
  { signature = constantˡ S s
  ; structure = Product.※-isHomomorphism
      (constant-isHomomorphism S s)
      Morphism.id-isHomomorphism
  }

constantˡ-Functor :
  ⦃ eqₜ : Equivalence 𝒯 e ⦄
  (T : Category.Signature 𝒯) → {S : Category.Signature 𝒮} →
  (isS : Category.Structure e′ S) →
  𝒮 .Ob → Functor T (Product.Category S T)
constantˡ-Functor T {S} isS s = record
  { signature = constantˡ S s
  ; structure = Product.※-isFunctor
      (constant-isFunctor T isS s)
      (Morphism.id-isFunctor T)
  ; isHomomorphism = Homomorphism.structure (constantˡ-Homomorphism S s)
  }

constantʳ-Homomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  Category.Signature 𝒮 → 𝒮 .Ob → Homomorphism 𝒯 (Product.𝒬 𝒯 𝒮)
constantʳ-Homomorphism S s = record
  { signature = constantʳ S s
  ; structure = Product.※-isHomomorphism
      Morphism.id-isHomomorphism
      (constant-isHomomorphism S s)
  }

constantʳ-Functor :
  ⦃ eqₜ : Equivalence 𝒯 e ⦄
  (T : Category.Signature 𝒯) → {S : Category.Signature 𝒮} →
  (isS : Category.Structure e′ S) →
  𝒮 .Ob → Functor T (Product.Category T S)
constantʳ-Functor T {S} isS s = record
  { signature = constantʳ S s
  ; structure = Product.※-isFunctor
      (Morphism.id-isFunctor T)
      (constant-isFunctor T isS s)
  ; isHomomorphism = Homomorphism.structure (constantʳ-Homomorphism S s)
  }

