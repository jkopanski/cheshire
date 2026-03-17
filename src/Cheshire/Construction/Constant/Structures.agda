{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Constant.Structures where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)

import Cheshire.Construction.Product.Signatures as Product

open import Cheshire.Construction.Constant.Signatures
open Morphism using (IsHomomorphism; IsFunctor)

private
  variable
    o ℓ e e′ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ

constant-isHomomorphism :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ →
  (T : Category.Signature 𝒯) → (t : 𝒯 .Ob) →
  IsHomomorphism ⦃ eqₛ ⦄ (constant T t)
constant-isHomomorphism ⦃ _ ⦄ ⦃ eqₜ ⦄ T t = record
  { F-resp-≈ = λ _ → eqₜ.refl } where module eqₜ = Equivalence eqₜ

constant-isFunctor :
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ →
  (S : Category.Signature 𝒮) {T : Category.Signature 𝒯} →
  (isT : Category.Structure e′ T) →
  (t : 𝒯 .Ob) → IsFunctor S T (constant T t)
constant-isFunctor S isT t = record
  { F-resp-id = eqₜ.refl
  ; F-resp-∘ = eqₜ.sym T.identityˡ
  } where module T = Category.Structure isT
          module eqₜ = Equivalence T.eq

-- TODO: constant{ˡ,ʳ}-is{Homomorphism,Functor}
