{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Natural.Signatures
open import Cheshire.Homomorphism.Signatures hiding (_∘_)

module Cheshire.Natural.Structures
  {o ℓ o′ ℓ′ : 𝕃.t} {𝒮 : Quiver o  ℓ } {𝒯 : Quiver o′ ℓ′}
  {ℱ 𝒢 : Morphism 𝒮 𝒯}
  where

open import Cheshire.Signatures

module _
  {e′} ⦃ eqₜ : Equivalence 𝒯 e′ ⦄
  where

  record IsNatural
    {S : Category 𝒮} {T : Category 𝒯}
    (N : ℱ ⇉ 𝒢) :
    Set (o ⊔ ℓ ⊔ e′) where
    open Category T
    open Quiver 𝒮
    open _⇉_ N
    module F = Morphism ℱ
    module G = Morphism 𝒢
    field
      commute : ∀ {X Y : 𝒮 .Ob} (f : X ⇒ Y) → η Y ∘ F.₁ f ≈ G.₁ f ∘ η X
