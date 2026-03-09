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
  {𝒞 : Quiver o ℓ} {𝒟 : Quiver o′ ℓ′} {ℰ : Quiver o″ ℓ″}
  (C : Category.t e 𝒞) (D : Category.t e′ 𝒟) (E : Category.t e″ ℰ)
  where

  private
    module C = Category.t C
    module D = Category.t D
    module E = Category.t E
    𝒞×𝒟 = Product.𝒬 𝒞 𝒟
    C×D = Product.Category C.signature D.signature

  bifunctor-Bifunctor :
    {H : Morphism.t 𝒞×𝒟 ℰ} →
    Morphism.IsFunctor H (Product.equivalence C.eq D.eq) E.eq C×D E.signature →
    Bifunctor.t C D E
  bifunctor-Bifunctor {H} isH = record
    { signature = bifunctor C.signature D.signature H
    ; structure = bifunctor-isBifunctor C D E.signature E.eq isH
    }
