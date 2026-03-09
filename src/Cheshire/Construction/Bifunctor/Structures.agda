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
  {𝒞 : Quiver o ℓ} {𝒟 : Quiver o′ ℓ′} {ℰ : Quiver o″ ℓ″}
  (C : Category.t e 𝒞) (D : Category.t e′ 𝒟) (E : Category.Signature ℰ)
  (eqᵉ : Equivalence ℰ e″)
  where

  private
    module C = Category.t C
    module D = Category.t D
    module eqᵉ = Equivalence eqᵉ
    C×D = Product.Category C.signature D.signature

  bifunctor-isBifunctor :
    {H : Morphism.t (Product.𝒬 𝒞 𝒟) ℰ} →
    (isH : Morphism.IsFunctor H (Product.equivalence C.eq D.eq) eqᵉ C×D E) →
    IsBifunctor {C = C.signature} {D = D.signature} {E = E} C.eq D.eq eqᵉ (bifunctor C.signature D.signature H)
  bifunctor-isBifunctor isH = record
    { resp-≈ˡ = λ f≈g → F-resp-≈ (f≈g , D.refl)
    ; resp-≈ʳ = λ f≈g → F-resp-≈ (C.refl , f≈g)
    ; resp-∘ˡ = eqᵉ.trans (F-resp-≈ (C.refl , D.sym D.identityˡ)) F-resp-∘
    ; resp-∘ʳ = eqᵉ.trans (F-resp-≈ (C.sym C.identityˡ , D.refl)) F-resp-∘
    } where open Morphism.IsFunctor isH
