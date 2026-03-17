{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism.Bundles where

import Data.Product as ×
open × using (Σ-syntax)

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Cartesian.Signature as CartesianCat renaming (Cartesian to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
open import Cheshire.Homomorphism.Structures

private
  variable
    o ℓ e : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ

record Homomorphism
  {o ℓ e o′ ℓ′ e′}
  (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′)
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ :
  Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    signature : Morphism.t 𝒮 𝒯
    structure : IsHomomorphism signature

  open Morphism.t signature public
  open IsHomomorphism structure public


record Functor
  {o ℓ e o′ ℓ′ e′}
  {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄
  (S : Category.t 𝒮) (T : Category.t 𝒯) :
  Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    signature      : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism signature
    structure      : IsFunctor S T signature

  open Morphism.t signature public
  open IsHomomorphism isHomomorphism public
  open IsFunctor structure public


record Cartesian
  {o ℓ e o′ ℓ′ e′}
  {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  {𝒮′ : Category.t 𝒮} {𝒯′ : Category.t 𝒯}
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄
  (S : CartesianCat.t 𝒮′) (T : CartesianCat.t 𝒯′) :
  Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module S = CartesianCat.t S
    module T = CartesianCat.t T

  field
    signature      : Morphism.t 𝒮 𝒯
    isHomomorphism : IsHomomorphism signature
    isFunctor      : IsFunctor 𝒮′ 𝒯′ signature
    structure      : IsCartesian S T signature

  open Morphism.t signature public
  open IsHomomorphism isHomomorphism public
  open IsFunctor isFunctor public
  open IsCartesian structure public

