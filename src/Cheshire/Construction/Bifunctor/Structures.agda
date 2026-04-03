{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Bifunctor.Structures where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product as Product

open import Cheshire.Bifunctor.Structure
open import Cheshire.Construction.Bifunctor.Signatures

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    e e′ e″ : 𝕃.t

module _
  {ℰ : Quiver o″ ℓ″}
  (C : Category.t o ℓ e) (D : Category.t o′ ℓ′ e′) (E : Category.Signature ℰ)
  ⦃ eqᵉ : Equivalence ℰ e″ ⦄
  where

  private
    module C = Category.t C
    module D = Category.t D
    𝒞 = C.𝒬
    𝒟 = C.𝒬
    module eqᵉ = Equivalence eqᵉ
    C×D = Product.Category C.category D.category

  bifunctor-isBifunctor :
    (H : Morphism.Functor C×D E) →
    (let module H = Morphism.Functor H) →
    IsBifunctor C.category D.category E (bifunctor C.category D.category H.morphism)
  bifunctor-isBifunctor H = record
    { resp-≈ˡ = λ f≈g → F-resp-≈ (f≈g , D.refl)
    ; resp-≈ʳ = λ f≈g → F-resp-≈ (C.refl , f≈g)
    ; resp-∘ˡ = eqᵉ.trans (F-resp-≈ (C.refl , D.sym D.identityˡ)) F-resp-∘
    ; resp-∘ʳ = eqᵉ.trans (F-resp-≈ (C.sym C.identityˡ , D.refl)) F-resp-∘
    } where open Morphism.Functor H

-- TODO: reduce-×-isBifunctor
--     , flip-isBifunctor
--     , {appʳ,appˡ}-is{Homomorphism,Functor}
--     , overlap-×-is{Homomorphism,Functor}
