{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Natural.Signatures
open import Cheshire.Homomorphism.Signatures

module Cheshire.Natural.Structures
  {o ℓ o′ ℓ′ : 𝕃.t} {𝒮 : Quiver o  ℓ } {𝒯 : Quiver o′ ℓ′}
  {F G : Morphism 𝒮 𝒯}
  (N : F ⇉ G)
  where

import Cheshire.Signatures as Sig

open _⇉_ N

module F = Morphism F
module G = Morphism G

record IsNatural
  (S : Sig.Category 𝒮) (T : Sig.Category 𝒯)
  {e′} (eqₜ : Equivalence 𝒯 e′) :
  Set (o ⊔ ℓ ⊔ e′) where
  open Sig.Category T
  open Quiver 𝒮
  private instance _ = eqₜ
  field
    commute : ∀ {X Y : Ob} (f : X ⇒ Y) → η Y ∘ F.₁ f ≈ G.₁ f ∘ η X
