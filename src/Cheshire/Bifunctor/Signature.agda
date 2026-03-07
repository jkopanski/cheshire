{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Bifunctor.Signature where

import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product as Product

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t

record Bifunctor
  (𝒞 : Quiver o ℓ) (𝒟 : Quiver o′ ℓ′) (ℰ : Quiver o″ ℓ″)
  : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″)
  where
  field
    H : Morphism.t (Product.𝒬 𝒞 𝒟) ℰ

  private
    module H = Morphism.t H

  field
    appˡ : 𝒞 .Ob → Morphism.t 𝒟 ℰ
    appʳ : 𝒟 .Ob → Morphism.t 𝒞 ℰ
    ₁ˡ : ∀ {A B d} (f : 𝒞 [ A , B ]) → ℰ [ H.₀ (A , d) , H.₀ (B , d) ]
    ₁ʳ : ∀ {A B c} (f : 𝒟 [ A , B ]) → ℰ [ H.₀ (c , A) , H.₀ (c , B) ]

    -- If 𝒞 and 𝒟 are categories those can be defined automatically.
    -- It is done in the Cheshire.Construction.Bifunctor
    -- appˡ c = H ∘M (constantˡ C c)
    -- appʳ d = H ∘M (constantʳ D d)
    -- ₁ˡ f = F₁ (f , D.id)
    -- ₁ʳ f = F₁ (C.id , f)
