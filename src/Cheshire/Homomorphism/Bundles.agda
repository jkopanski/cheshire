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
  {o ℓ o′ ℓ′}
  (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′)
  (e : 𝕃.t) (e′ : 𝕃.t)
    : Set (𝕃.levelOfTerm 𝒮 ⊔ 𝕃.suc e ⊔ 𝕃.levelOfTerm 𝒯 ⊔ 𝕃.suc e′) where
  no-eta-equality
  field
    instance eqₛ   : Equivalence 𝒮 e
    instance eqₜ   : Equivalence 𝒯 e′
    morphism       : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism eqₛ eqₜ morphism

  open Morphism.t morphism public
  open IsHomomorphism isHomomorphism public


record Functor
  {o ℓ o′ ℓ′}
  {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (S : Category.t 𝒮) (T : Category.t 𝒯)
  (e : 𝕃.t) (e′ : 𝕃.t)
    : Set (𝕃.levelOfTerm S ⊔ 𝕃.suc e ⊔ 𝕃.levelOfTerm T ⊔ 𝕃.suc e′) where
  no-eta-equality
  field
    instance eqₛ   : Equivalence 𝒮 e
    instance eqₜ   : Equivalence 𝒯 e′
    morphism       : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism eqₛ eqₜ morphism
    isFunctor      : IsFunctor eqₛ eqₜ S T morphism

  open Morphism.t morphism public
  open IsHomomorphism isHomomorphism public
  open IsFunctor isFunctor public


record Cartesian
  {o ℓ o′ ℓ′}
  {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  {𝒮′ : Category.t 𝒮} {𝒯′ : Category.t 𝒯}
  (S : CartesianCat.t 𝒮′) (T : CartesianCat.t 𝒯′)
  (e : 𝕃.t) (e′ : 𝕃.t)
    : Set (𝕃.levelOfTerm S ⊔ 𝕃.suc e ⊔ 𝕃.levelOfTerm T ⊔ 𝕃.suc e′) where
  no-eta-equality
  private
    module S = CartesianCat.t S
    module T = CartesianCat.t T

  field
    instance eqₛ   : Equivalence 𝒮 e
    instance eqₜ   : Equivalence 𝒯 e′
    morphism       : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism eqₛ eqₜ morphism
    isFunctor      : IsFunctor eqₛ eqₜ 𝒮′ 𝒯′ morphism
    isCartesian    : IsCartesian eqₛ eqₜ S T morphism

  open Morphism.t morphism public
  open IsHomomorphism isHomomorphism public
  open IsFunctor isFunctor public
  open IsCartesian isCartesian public
