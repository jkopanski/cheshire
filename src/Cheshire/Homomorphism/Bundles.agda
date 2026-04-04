{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism.Bundles where

import Data.Product as ×
open × using (Σ-syntax)

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Cartesian.Signature as CartesianCat renaming (Cartesian to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
open import Cheshire.Homomorphism.Structures

record Homomorphism
  {o ℓ e o′ ℓ′ e′}
  (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′)
  (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′)
    : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  no-eta-equality
  field
    morphism       : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism eqₛ eqₜ morphism

  open Morphism.t morphism public
  open IsHomomorphism isHomomorphism public


record Functor
  {o ℓ e o′ ℓ′ e′}
  {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′)
  (S : Category.t 𝒮) (T : Category.t 𝒯)
    : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  no-eta-equality
  field
    morphism       : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism eqₛ eqₜ morphism
    isFunctor      : IsFunctor eqₛ eqₜ S T morphism

  open Morphism.t morphism public
  open IsHomomorphism isHomomorphism public
  open IsFunctor isFunctor public


record Cartesian
  {o ℓ e o′ ℓ′ e′}
  {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′)
  {𝒮′ : Category.t 𝒮} {𝒯′ : Category.t 𝒯}
  (S : CartesianCat.t 𝒮′) (T : CartesianCat.t 𝒯′)
    : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  no-eta-equality
  private
    module S = CartesianCat.t S
    module T = CartesianCat.t T

  field
    morphism       : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism eqₛ eqₜ morphism
    isFunctor      : IsFunctor eqₛ eqₜ 𝒮′ 𝒯′ morphism
    isCartesian    : IsCartesian eqₛ eqₜ S T morphism

  open Morphism.t morphism public
  open IsHomomorphism isHomomorphism public
  open IsFunctor isFunctor public
  open IsCartesian isCartesian public

