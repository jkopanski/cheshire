{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Bifunctor.Signature where

import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product.Signatures as Product

open Morphism using (id; _∘_)
open Product using (_※_; _⁂_)

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    𝒜 ℬ : Quiver o ℓ

record Bifunctor
  (𝒞 : Quiver o ℓ) (𝒟 : Quiver o′ ℓ′) (ℰ : Quiver o″ ℓ″)
  : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″)
  where
  field
    H : Morphism.t (Product.𝒬 𝒞 𝒟) ℰ

  open Morphism.t H public

  field
    appˡ : 𝒞 .Ob → Morphism.t 𝒟 ℰ
    appʳ : 𝒟 .Ob → Morphism.t 𝒞 ℰ
    ₁ˡ : ∀ {A B d} (f : 𝒞 [ A , B ]) → ℰ [ F₀ (A , d) , F₀ (B , d) ]
    ₁ʳ : ∀ {A B c} (f : 𝒟 [ A , B ]) → ℰ [ F₀ (c , A) , F₀ (c , B) ]

  overlap-× : (F : Morphism.t 𝒜 𝒞) → (G : Morphism.t 𝒜 𝒟) → Morphism.t 𝒜 ℰ
  overlap-× F G = H ∘ (F ※ G)

  flip : Bifunctor 𝒟 𝒞 ℰ
  flip = record
    { H = H′
    ; appˡ = appʳ
    ; appʳ = appˡ
    ; ₁ˡ = ₁ʳ
    ; ₁ʳ = ₁ˡ
    } where H′ : Morphism.t (Product.𝒬 𝒟 𝒞) ℰ
            H′ = record
              { F₀ = λ (X , Y) → F₀ (Y , X)
              ; F₁ = λ (f , g) → F₁ (g , f)
              }
