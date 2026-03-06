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
  (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′) →
  Category.Signature 𝒯 → 𝒯 .Ob → Homomorphism eqₛ eqₜ
constant-Homomorphism eqₛ eqₜ T t = record
  { signature = constant T t
  ; structure = constant-isHomomorphism eqₛ eqₜ T t
  }

constant-Functor :
  (eqₛ : Equivalence 𝒮 e)
  (S : Category.Signature 𝒮) → {T : Category.Signature 𝒯} →
  (isT : Category.Structure e′ T) →
  𝒯 .Ob → Functor eqₛ (Category.Structure.eq isT) S T
constant-Functor eqₛ S {T} isT t = record
  { signature = constant T t
  ; structure = constant-isFunctor eqₛ S isT t
  }

constant!-Homomorphism :
  (eqₜ : Equivalence 𝒯 e′) →
  Category.Signature 𝒯 → 𝒯 .Ob → Homomorphism (One.eq {e = e}) eqₜ
constant!-Homomorphism eqₜ T t = record
  { signature = constant! T t
  ; structure = constant-isHomomorphism One.eq eqₜ T t
  }

constant!-Functor :
  (S : Category.Signature 𝒮) → {T : Category.Signature 𝒯} →
  (isT : Category.Structure e′ T) →
  𝒯 .Ob → Functor (One.eq {e = e}) (Category.Structure.eq isT) One.t T
constant!-Functor S {T} isT t = record
  { signature = constant! T t
  ; structure = constant-isFunctor One.eq One.t isT t
  }

constantˡ-Homomorphism :
  (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′) →
  Category.Signature 𝒮 → 𝒮 .Ob → Homomorphism eqₜ (Product.equivalence eqₛ eqₜ)
constantˡ-Homomorphism eqₛ eqₜ S s = record
  { signature = constantˡ S s
  ; structure = Product.※-isHomomorphism
      (constant-isHomomorphism eqₜ eqₛ S s)
      (Morphism.id-isHomomorphism eqₜ)
  }

constantˡ-Functor :
  (eqₜ : Equivalence 𝒯 e)
  (T : Category.Signature 𝒯) → {S : Category.Signature 𝒮} →
  (isS : Category.Structure e′ S) →
  𝒮 .Ob → Functor eqₜ (Product.equivalence (Category.Structure.eq isS) eqₜ) T (Product.Category S T)
constantˡ-Functor eqₜ T {S} isS s = record
  { signature = constantˡ S s
  ; structure = Product.※-isFunctor
      (constant-isFunctor eqₜ T isS s)
      (Morphism.id-isFunctor T eqₜ)
  }

constantʳ-Homomorphism :
  (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′) →
  Category.Signature 𝒮 → 𝒮 .Ob → Homomorphism eqₜ (Product.equivalence eqₜ eqₛ)
constantʳ-Homomorphism eqₛ eqₜ S s = record
  { signature = constantʳ S s
  ; structure = Product.※-isHomomorphism
      (Morphism.id-isHomomorphism eqₜ)
      (constant-isHomomorphism eqₜ eqₛ S s)
  }

constantʳ-Functor :
  (eqₜ : Equivalence 𝒯 e)
  (T : Category.Signature 𝒯) → {S : Category.Signature 𝒮} →
  (isS : Category.Structure e′ S) →
  𝒮 .Ob → Functor eqₜ (Product.equivalence eqₜ (Category.Structure.eq isS)) T (Product.Category T S)
constantʳ-Functor eqₜ T {S} isS s = record
  { signature = constantʳ S s
  ; structure = Product.※-isFunctor
      (Morphism.id-isFunctor T eqₜ)
      (constant-isFunctor eqₜ T isS s)
  }

