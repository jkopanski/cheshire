{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Signatures where

open import Cheshire.Homomorphism.Signatures

module _
  {o ℓ o′ ℓ′ : 𝕃.t}
  {𝒮 : Quiver o  ℓ }
  {𝒯 : Quiver o′ ℓ′} where

  open Quiver using (Ob)
  open Quiver 𝒯

  record _⇉_ (F : Morphism 𝒮 𝒯) (G : Morphism 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    constructor mk⇉
    private
      module F = Morphism F
      module G = Morphism G

    field
      η : ∀ (X : 𝒮 .Ob) → F.₀ X ⇒ G.₀ X
