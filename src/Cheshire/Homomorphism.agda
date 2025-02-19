{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism where

open import Relation.Binary.PropositionalEquality.Subst.Properties
  using (module Shorthands)
open import Cheshire.Homomorphism.Signatures renaming (id to idM; _∘_ to _∘M_) public
open import Cheshire.Homomorphism.Structures public
open import Cheshire.Homomorphism.Bundles public

-- Copied from agda-categories:
-- https://agda.github.io/agda-categories/Data.Quiver.Morphism.html#2527
-- which is licensed under the MIT license.
--   Copyright (c) 2019 Agda Github Community

open Rel₂ using (_≡_)

private
  variable
    o ℓ o′ ℓ′ e′ o″ ℓ″ : 𝕃.t

infix 4 _≃_
record _≃_
  {𝒬 : Quiver o ℓ} {𝒬′ : Quiver o′ ℓ′}
  ⦃ eq : Equivalence 𝒬′ e′ ⦄
  (ℳ ℳ′ : Morphism 𝒬 𝒬′)
  : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module M  = Morphism ℳ
    module M′ = Morphism ℳ′
    instance _ = eq
  open Shorthands (𝒬′ .Hom)

  field
    F₀≡ : ∀ {X} → M.₀ X ≡ M′.₀ X
    F₁≡ : ∀ {A B} {f : 𝒬 .Hom A B} → M.₁ f ▸ F₀≡ ≈ F₀≡ ◂ M′.₁ f
