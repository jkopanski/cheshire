{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Bifunctor.Bundles where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Bifunctor as Bifunctor renaming (Bifunctor to t)
import Cheshire.Construction.Product as Product

open import Cheshire.Construction.Bifunctor.Signatures
open import Cheshire.Construction.Bifunctor.Structures

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    e e′ e″ : 𝕃.t

module _
  (C : Category.t o ℓ e) (D : Category.t o′ ℓ′ e′) (E : Category.t o″ ℓ″ e″)
  where

  private
    module C = Category.t C
    module D = Category.t D
    module E = Category.t E
    𝒞×𝒟 = Product.𝒬 C.𝒬 D.𝒬
    C×D = Product.Category C.category D.category
    eq× = Product.equivalence C.eq D.eq

  bifunctor-Bifunctor :
    (H : Morphism.Functor eq× E.eq C×D E.category) →
    Bifunctor.t C D E
  bifunctor-Bifunctor H = record
    { signature = bifunctor C.category D.category H.morphism
    ; structure = bifunctor-isBifunctor C D E.category H
    } where module H = Morphism.Functor H
