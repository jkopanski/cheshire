{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Structures where

import Cheshire.Bundles as Bundles
import Cheshire.Signatures as Signatures
import Cheshire.Structures as Structures
import Cheshire.Category.Structure as IsCategory renaming (IsCategory to t)
import Cheshire.Morphism.Structures as Morphisms
import Cheshire.Morphism.Bundles as MorphismBundles
import Cheshire.Natural.Signatures as Natural

open import Cheshire.Natural.Signatures
open import Cheshire.Homomorphism.Signatures renaming (_∘_ to _∘F_)

private
  variable
    o o′ ℓ ℓ′ e : 𝕃.t

module _
  {𝒮 : Quiver o  ℓ } {𝒯 : Quiver o′ ℓ′} {ℱ 𝒢 : Morphism 𝒮 𝒯}
  -- Is category bundle better here?
  {T : Signatures.Category 𝒯}
  {e} (isT : IsCategory.t e T)
  where

  private
    module F = Morphism ℱ
    module G = Morphism 𝒢

    open Quiver 𝒮
    open Signatures.Category T

  record IsTransformation (N : Natural.Transformation ℱ 𝒢) : Set (o ⊔ ℓ ⊔ e) where
    no-eta-equality
    open Natural.Transformation N

    field
      commute : ∀ {X Y : 𝒮 .Ob} (f : X ⇒ Y) → η Y ∘ F.₁ f ≈ G.₁ f ∘ η X

module _
  {𝒮 : Quiver o  ℓ } {𝒯 : Quiver o′ ℓ′} {ℱ 𝒢 : Morphism 𝒮 𝒯}
  {T : Signatures.Category 𝒯}
  {e} (isT : IsCategory.t e T)
  where

  private
    module F = Morphism ℱ
    module G = Morphism 𝒢

    open MorphismBundles T

  record IsIsomorphism (I : Natural.Isomorphism ℱ 𝒢) : Set (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e) where
    no-eta-equality
    module I = Natural.Isomorphism I

    field
      F⇒G : IsTransformation isT I.F⇒G
      F⇐G : IsTransformation isT I.F⇐G

    field
      iso : ∀ X → Morphisms.IsIso T (I.iso.from X) (I.iso.to X)

    module isIso X = Morphisms.IsIso (iso X)

    FX≅GX : ∀ {X} → F.₀ X ≅ G.₀ X
    FX≅GX {X} = record
      { isIso X
      ; isIso = iso X
      }
