{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Natural.Signatures where

open import Cheshire.Homomorphism.Signatures

module _
  {o ℓ o′ ℓ′ : 𝕃.t}
  {𝒮 : Quiver o  ℓ }
  {𝒯 : Quiver o′ ℓ′}
  where

  record _⇉_ (ℱ : Morphism 𝒮 𝒯) (𝒢 : Morphism 𝒮 𝒯) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    constructor mk⇉
    private
      module F = Morphism ℱ
      module G = Morphism 𝒢

    field
      η : ∀ (X : 𝒮 .Ob) → 𝒯 .Hom (F.₀ X) (G.₀ X)
