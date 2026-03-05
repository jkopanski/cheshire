{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Bundles
  {o ℓ o′ ℓ′ : 𝕃.t}
  {𝒮 : Quiver o  ℓ } {𝒯 : Quiver o′ ℓ′}
  where

open import Cheshire.Bundles
import Cheshire.Homomorphism.Signatures as Homo
import Cheshire.Natural.Signatures as Signatures
import Cheshire.Natural.Structures as Structures

module _ {e} (T : Category e 𝒯) where

  module T = Category T

  record NaturalTransformation (ℱ : Homo.Morphism 𝒮 𝒯) (𝒢 : Homo.Morphism 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e) where
    field
      signature : Signatures.Transformation ℱ 𝒢
      structure : Structures.IsTransformation T.structure signature

    open Signatures.Transformation signature public
    open Structures.IsTransformation structure public

  record NaturalIsomorphism (ℱ : Homo.Morphism 𝒮 𝒯) (𝒢 : Homo.Morphism 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e) where
    field
      signature : Signatures.Isomorphism ℱ 𝒢
      structure : Structures.IsIsomorphism T.structure signature

    open Signatures.Isomorphism signature public
    open Structures.IsIsomorphism structure public
