{-# OPTIONS --safe #-}

-- I have no idea why agda-categories doesn't put this under
-- Construction hierarchy.

open import Cheshire.Core

module Cheshire.Construction.Product.Signatures where

import Data.Product as ×
import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)

open × using (_×_; _,_; <_,_>; proj₁; proj₂)

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t

𝒬 : (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) → Quiver (o ⊔ o′) (ℓ ⊔ ℓ′)
𝒬 𝒮 𝒯 = record
  { Ob = 𝒮 .Ob × 𝒯 .Ob
  ; Hom = ×.zipWith (𝒮 .Hom) (𝒯 .Hom) _×_
  }

private
  variable
    𝒮 𝒯 : Quiver o ℓ
    𝒮₁ 𝒯₁ : Quiver o ℓ
    𝒮₂ 𝒯₂ : Quiver o ℓ

Category : (S : Category.t 𝒮) (T : Category.t 𝒯) → Category.t (𝒬 𝒮 𝒯)
Category S T = record
  { id = S.id , T.id
  ; _∘_ = ×.zip S._∘_ T._∘_
  } where module S = Category.t S
          module T = Category.t T

infixr 2 _※_
_※_ : (F : Morphism.t 𝒮 𝒯₁) → (G : Morphism.t 𝒮 𝒯₂) → Morphism.t 𝒮 (𝒬 𝒯₁ 𝒯₂)
F ※ G = record
  { F₀ = < F.₀ , G.₀ >
  ; F₁ = < F.₁ , G.₁ >
  } where module F = Morphism.t F
          module G = Morphism.t G

infixr 2 _⁂_
_⁂_ : (F : Morphism.t 𝒮₁ 𝒯₁) → (G : Morphism.t 𝒮₂ 𝒯₂) → Morphism.t (𝒬 𝒮₁ 𝒮₂) (𝒬 𝒯₁ 𝒯₂)
F ⁂ G = record
  { F₀ = ×.map F.₀ G.₀
  ; F₁ = ×.map F.₁ G.₁
  } where module F = Morphism.t F
          module G = Morphism.t G

module _ (C₁ : Quiver o ℓ) (C₂ : Quiver o′ ℓ′) (C₃ : Quiver o″ ℓ″) where

  assocˡ : Morphism.t (𝒬 (𝒬 C₁ C₂) C₃) (𝒬 C₁ (𝒬 C₂ C₃))
  assocˡ = record
    { F₀ = < proj₁ ⊙ proj₁ , < proj₂ ⊙ proj₁ , proj₂ > >
    ; F₁ = < proj₁ ⊙ proj₁ , < proj₂ ⊙ proj₁ , proj₂ > >
    }

  assocʳ : Morphism.t (𝒬 C₁ (𝒬 C₂ C₃)) (𝒬 (𝒬 C₁ C₂) C₃)
  assocʳ = record
    { F₀ = < < proj₁ , proj₁ ⊙ proj₂ > , proj₂ ⊙ proj₂ >
    ; F₁ = < < proj₁ , proj₁ ⊙ proj₂ > , proj₂ ⊙ proj₂ >
    }

module _ (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) where

  πˡ : Morphism.t (𝒬 𝒮 𝒯) 𝒮
  πˡ = record
    { F₀ = proj₁
    ; F₁ = proj₁
    }

  πʳ : Morphism.t (𝒬 𝒮 𝒯) 𝒯
  πʳ = record
    { F₀ = proj₂
    ; F₁ = proj₂
    }

  Swap : Morphism.t (𝒬 𝒮 𝒯) (𝒬 𝒯 𝒮)
  Swap = record
    { F₀ = ×.swap
    ; F₁ = ×.swap
    }
