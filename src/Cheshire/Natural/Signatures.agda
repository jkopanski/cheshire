{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Signatures where

open import Cheshire.Signatures
open import Cheshire.Homomorphism.Signatures renaming (id to idF; _∘_ to _∘F_)

import Cheshire.Morphism.Signatures as Morphisms

open Morphism

module _
  {o ℓ o′ ℓ′ : 𝕃.t}
  {𝒮 : Quiver o  ℓ }
  {𝒯 : Quiver o′ ℓ′}
  where

  record Transformation (ℱ : Morphism 𝒮 𝒯) (𝒢 : Morphism 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    private
      module F = Morphism ℱ
      module G = Morphism 𝒢

    field
      η : ∀ (X : 𝒮 .Ob) → 𝒯 .Hom (F.₀ X) (G.₀ X)

private
  variable
    o ℓ : 𝕃.t
    C D E : Quiver o ℓ

id : ∀ {F : Morphism C D} {𝒟 : Category D} → Transformation F F
id {𝒟 = 𝒟} = record { η = λ _ → D.id } where module D = Category 𝒟

_∘ᵥ_ :
  ∀ {F G H : Morphism C D} {𝒟 : Category D} →
  Transformation G H → Transformation F G → Transformation F H
_∘ᵥ_ {𝒟 = 𝒟} X Y = record
  { η = λ q → 𝒟 [ X.η q ∘ Y.η q ]
  } where module X = Transformation X
          module Y = Transformation Y

_∘ₕ_ :
  ∀ {F G : Morphism C D} {H I : Morphism D E} {ℰ : Category E} →
  Transformation H I → Transformation F G → Transformation (H ∘F F) (I ∘F G)
_∘ₕ_ {E = E} {F} {I = I} {ℰ = ℰ} Y X = record
  { η = λ q → ℰ [ I.₁ (X.η q) ∘ Y.η (F.₀ q) ]
  } where module X = Transformation X
          module Y = Transformation Y
          module F = Morphism F
          module I = Morphism I

_∘ˡ_ :
  ∀ {G H : Morphism C D} →
  (F : Morphism D E) → Transformation G H → Transformation (F ∘F G) (F ∘F H)
_∘ˡ_ F α = record
  { η = λ X → F.₁ (η X)
  } where module F = Morphism F
          open Transformation α

_∘ʳ_
  : ∀ {G H : Morphism D E} →
  Transformation G H → (F : Morphism C D) → Transformation (G ∘F F) (H ∘F F)
_∘ʳ_ α F = record
  { η = λ X → η (F.₀ X)
  } where module F = Morphism F
          open Transformation α

module _
  {o ℓ o′ ℓ′ : 𝕃.t}
  {𝒮 : Quiver o  ℓ }
  {𝒯 : Quiver o′ ℓ′}
  where

  record Isomorphism (ℱ : Morphism 𝒮 𝒯) (𝒢 : Morphism 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    private
      module F = Morphism ℱ
      module G = Morphism 𝒢
      open Morphisms 𝒯

    field
      F⇒G : Transformation ℱ 𝒢
      F⇐G : Transformation 𝒢 ℱ

    module ⇒ = Transformation F⇒G
    module ⇐ = Transformation F⇐G

    field
      iso : ∀ X → F.₀ X ⇔ G.₀ X

    module iso X = _⇔_ (iso X)
