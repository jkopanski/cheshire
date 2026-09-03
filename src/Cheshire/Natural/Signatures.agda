{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Signatures where

open import Cheshire.Category.Signature
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
    o″ ℓ″ : 𝕃.t
    C D E : Quiver o″ ℓ″

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

module Compose (𝒟 : Category D) where

  private module D = Category 𝒟

  id : ∀ {F : Morphism C D} → Transformation F F
  id = record { η = λ _ → D.id }

  _∘ᵥ_ :
    ∀ {F G H : Morphism C D} →
    Transformation G H → Transformation F G → Transformation F H
  _∘ᵥ_ X Y = record
    { η = λ q → 𝒟 [ X.η q ∘ Y.η q ]
    } where module X = Transformation X
            module Y = Transformation Y

  _∘ₕ_ :
    ∀ {F G : Morphism C E} {H I : Morphism E D} →
    Transformation H I → Transformation F G → Transformation (H ∘F F) (I ∘F G)
  _∘ₕ_ {E = E} {F} {I = I} Y X = record
    { η = λ q → 𝒟 [ I.₁ (X.η q) ∘ Y.η (F.₀ q) ]
    } where module X = Transformation X
            module Y = Transformation Y
            module F = Morphism F
            module I = Morphism I


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

    iso : ∀ X → F.₀ X ⇔ G.₀ X
    iso x = record
      { from = ⇒.η x
      ; to = ⇐.η x
      }

    module iso X = _⇔_ (iso X)
