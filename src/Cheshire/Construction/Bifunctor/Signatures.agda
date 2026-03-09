{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Bifunctor.Signatures where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Bifunctor.Signature as Bifunctor renaming (Bifunctor to t)
import Cheshire.Construction.Constant.Signatures as Constant
import Cheshire.Construction.Product.Signatures as Product

open Constant using (constantˡ; constantʳ)
open Product using (_※_; _⁂_)
open Morphism using (id; _∘_)

private
  variable
   o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
   𝒞 𝒟 ℰ 𝒜 ℬ : Quiver o ℓ

module _ (C : Category.t 𝒞) (D : Category.t 𝒟) where

  bifunctor : (H : Morphism.t (Product.𝒬 𝒞 𝒟) ℰ) → Bifunctor.t 𝒞 𝒟 ℰ
  bifunctor H = record
    { H = H
    ; appˡ = λ c → H ∘ constantˡ C c
    ; appʳ = λ d → H ∘ constantʳ D d
    ; ₁ˡ = λ f → H.₁ (f , D.id)
    ; ₁ʳ = λ f → H.₁ (C.id , f)
    } where module H = Morphism.t H
            module C = Category.t C
            module D = Category.t D

module _ (A : Category.t 𝒜) (B : Category.t ℬ) where

  reduce-× : (F : Morphism.t 𝒜 𝒞) → (G : Morphism.t ℬ 𝒟) → (H : Bifunctor.t 𝒞 𝒟 ℰ) → Bifunctor.t 𝒜 ℬ ℰ
  reduce-× F G H = record
    { H = H′
    ; appˡ = λ a → H′ ∘ constantˡ A a
    ; appʳ = λ b → H′ ∘ constantʳ B b
    ; ₁ˡ = λ f → H.₁ˡ (F.₁ f)
    ; ₁ʳ = λ f → H.₁ʳ (G.F₁ f)
    } where module H = Bifunctor.t H
            module F = Morphism.t F
            module G = Morphism.t G
            H′ = H.H ∘ (F ⁂ G)
