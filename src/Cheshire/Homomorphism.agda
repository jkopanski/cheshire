{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism where

import Data.Product as ×
open import Relation.Binary.PropositionalEquality.Subst.Properties
  using (module Shorthands)
import Cheshire.Signatures as Signatures

open import Cheshire.Homomorphism.Signatures renaming (id to idM; _∘_ to _∘M_) public
open import Cheshire.Homomorphism.Structures public
open import Cheshire.Homomorphism.Bundles public

-- Copied from agda-categories:
-- https://agda.github.io/agda-categories/Data.Quiver.Morphism.html#2527
-- which is licensed under the MIT license.
--   Copyright (c) 2019 Agda Github Community

open × using (Σ-syntax)
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

module _
  {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″}
  ⦃ eq : Equivalence C e′ ⦄
  where

  infix 5 _∣ˡ_
  _∣ˡ_ : Morphism B C → Morphism A C → Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  G ∣ˡ F = Σ[ J ∈ Morphism A B ] G ∘M J ≃ F

id-isHomomorphism : {𝒬 : Quiver o ℓ} → (eq : Equivalence 𝒬 e′) → IsHomomorphism idM eq eq
id-isHomomorphism eq = record { F-resp-≈ = Function.id }

id-isFunctor :
  {𝒬 : Quiver o ℓ} →
  (C : Signatures.Category 𝒬) (eq : Equivalence 𝒬 e′) →
  IsFunctor idM eq eq C C
id-isFunctor _ eq = record
  { IsHomomorphism (id-isHomomorphism eq)
  ; F-resp-id = eq.refl
  ; F-resp-∘ = eq.refl
  } where module eq = Equivalence eq

