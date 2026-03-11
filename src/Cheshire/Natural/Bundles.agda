{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Bundles
  {o ℓ o′ ℓ′ : 𝕃.t}
  {𝒮 : Quiver o  ℓ } {𝒯 : Quiver o′ ℓ′}
  where

import Cheshire.Category.Bundle as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)
import Cheshire.Natural.Signatures as Signatures
import Cheshire.Natural.Structures as Structures
import Cheshire.Morphism as Morphisms

module _ {e} (T : Category.t e 𝒯) where

  module T = Category.t T

  record NaturalTransformation (ℱ : Morphism.t 𝒮 𝒯) (𝒢 : Morphism.t 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e) where
    field
      signature : Signatures.Transformation ℱ 𝒢
      structure : Structures.IsTransformation T.structure signature

    open Signatures.Transformation signature public
    open Structures.IsTransformation structure public

  record NaturalIsomorphism (ℱ : Morphism.t 𝒮 𝒯) (𝒢 : Morphism.t 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e) where
    field
      signature : Signatures.Isomorphism ℱ 𝒢
      structure : Structures.IsIsomorphism T.structure signature

    private
      module sig = Signatures.Isomorphism signature
      module struct = Structures.IsIsomorphism structure
      module F = Morphism.t ℱ
      module G = Morphism.t 𝒢
      open Morphisms.Bundles T.signature

    F⇒G : NaturalTransformation ℱ 𝒢
    F⇒G = record { signature = sig.F⇒G; structure = struct.F⇒G }
    F⇐G : NaturalTransformation 𝒢 ℱ
    F⇐G = record { signature = sig.F⇐G; structure = struct.F⇐G }

    module ⇒ = NaturalTransformation F⇒G
    module ⇐ = NaturalTransformation F⇐G

    iso : ∀ X → Morphisms.Structures.IsIso T.signature (sig.iso.from X) (sig.iso.to X)
    iso x = struct.iso x

    FX≅GX : ∀ {X} → F.₀ X ≅ G.₀ X
    FX≅GX = struct.FX≅GX

