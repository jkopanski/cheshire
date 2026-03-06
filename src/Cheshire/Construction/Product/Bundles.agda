{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Product.Bundles where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product.Signatures as Product

open import Cheshire.Construction.Product.Structures
open Product using (𝒬; _※_; _⁂_; assocˡ; assocʳ; πˡ; πʳ; Swap)
open Morphism using (Homomorphism; Functor)

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    e e′ e″ e‴ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ
    𝒮₁ 𝒯₁ : Quiver o ℓ
    𝒮₂ 𝒯₂ : Quiver o ℓ

Category :
  (S : Category.t e 𝒮) (T : Category.t e′ 𝒯) →
  Category.t (e ⊔ e′) (𝒬 𝒮 𝒯)
Category S T = record
  { signature = Product.Category S.signature T.signature
  ; structure = IsCategory S.structure T.structure
  } where module S = Category.t S
          module T = Category.t T

module _
  {eqₛ : Equivalence 𝒮 e} {eqₜ₁ : Equivalence 𝒯₁ e′} {eqₜ₂ : Equivalence 𝒯₂ e″}
  where

  ※-Homomorphism :
    (F : Homomorphism eqₛ eqₜ₁) (G : Homomorphism eqₛ eqₜ₂) →
    Homomorphism eqₛ (equivalence eqₜ₁ eqₜ₂)
  ※-Homomorphism F G = record
    { signature = F.signature ※ G.signature
    ; structure = ※-isHomomorphism F.structure G.structure
    } where module F = Homomorphism F
            module G = Homomorphism G

  ※-Functor :
    {S : Category.Signature 𝒮} {T₁ : Category.Signature 𝒯₁} {T₂ : Category.Signature 𝒯₂} →
    (F : Functor eqₛ eqₜ₁ S T₁) (G : Functor eqₛ eqₜ₂ S T₂) →
    Functor eqₛ (equivalence eqₜ₁ eqₜ₂) S (Product.Category T₁ T₂)
  ※-Functor F G = record
    { signature = F.signature ※ G.signature
    ; structure = ※-isFunctor F.structure G.structure
    } where module F = Functor F
            module G = Functor G

module _
  {eqₛ₁ : Equivalence 𝒮₁ e} {eqₛ₂ : Equivalence 𝒮₂ e′} {eqₜ₁ : Equivalence 𝒯₁ e″} {eqₜ₂ : Equivalence 𝒯₂ e‴}
  where

  ⁂-Homomorphism :
    (F : Homomorphism eqₛ₁ eqₜ₁) (G : Homomorphism eqₛ₂ eqₜ₂) →
    Homomorphism (equivalence eqₛ₁ eqₛ₂) (equivalence eqₜ₁ eqₜ₂)
  ⁂-Homomorphism F G = record
    { signature = F.signature ⁂ G.signature
    ; structure = ⁂-isHomomorphism F.structure G.structure
    } where module F = Homomorphism F
            module G = Homomorphism G

  ⁂-Functor :
    {S₁ : Category.Signature 𝒮₁} {S₂ : Category.Signature 𝒮₂} {T₁ : Category.Signature 𝒯₁} {T₂ : Category.Signature 𝒯₂} →
    (F : Functor eqₛ₁ eqₜ₁ S₁ T₁) (G : Functor eqₛ₂ eqₜ₂ S₂ T₂) →
    Functor
      (equivalence eqₛ₁ eqₛ₂) (equivalence eqₜ₁ eqₜ₂)
      (Product.Category S₁ S₂) (Product.Category T₁ T₂)
  ⁂-Functor F G = record
    { signature = F.signature ⁂ G.signature
    ; structure = ⁂-isFunctor F.structure G.structure
    } where module F = Functor F
            module G = Functor G

module _
  {C₁ : Quiver o ℓ} {C₂ : Quiver o′ ℓ′} {C₃ : Quiver o″ ℓ″}
  (eq₁ : Equivalence C₁ e) (eq₂ : Equivalence C₂ e′) (eq₃ : Equivalence C₃ e″)
  where

  assocˡ-Homomorphism :
    Homomorphism
      (equivalence (equivalence eq₁ eq₂) eq₃)
      (equivalence eq₁ (equivalence eq₂ eq₃))
  assocˡ-Homomorphism = record
    { signature = assocˡ C₁ C₂ C₃
    ; structure = assocˡ-isHomomorphism eq₁ eq₂ eq₃
    }

  assocˡ-Functor :
    (C₁′ : Category.Signature C₁) (C₂′ : Category.Signature C₂) (C₃′ : Category.Signature C₃) →
    Functor
      (equivalence (equivalence eq₁ eq₂) eq₃)
      (equivalence eq₁ (equivalence eq₂ eq₃))
      (Product.Category (Product.Category C₁′ C₂′) C₃′)
      (Product.Category C₁′ (Product.Category C₂′ C₃′))
  assocˡ-Functor C₁′ C₂′ C₃′ = record
    { signature = assocˡ C₁ C₂ C₃
    ; structure = assocˡ-isFunctor eq₁ eq₂ eq₃ C₁′ C₂′ C₃′
    }

  assocʳ-Homomorphism :
    Homomorphism
      (equivalence eq₁ (equivalence eq₂ eq₃))
      (equivalence (equivalence eq₁ eq₂) eq₃)
  assocʳ-Homomorphism = record
    { signature = assocʳ C₁ C₂ C₃
    ; structure = assocʳ-isHomomorphism eq₁ eq₂ eq₃
    }

  assocʳ-Functor :
    (C₁′ : Category.Signature C₁) (C₂′ : Category.Signature C₂) (C₃′ : Category.Signature C₃) →
    Functor
      (equivalence eq₁ (equivalence eq₂ eq₃))
      (equivalence (equivalence eq₁ eq₂) eq₃)
      (Product.Category C₁′ (Product.Category C₂′ C₃′))
      (Product.Category (Product.Category C₁′ C₂′) C₃′)
  assocʳ-Functor C₁′ C₂′ C₃′ = record
    { signature = assocʳ C₁ C₂ C₃
    ; structure = assocʳ-isFunctor eq₁ eq₂ eq₃ C₁′ C₂′ C₃′
    }

module _ (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′) where

  πˡ-Homomorphism :
    Homomorphism (equivalence eqₛ eqₜ) eqₛ
  πˡ-Homomorphism = record
    { signature = πˡ 𝒮 𝒯
    ; structure = πˡ-isHomomorphism eqₛ eqₜ
    }

  πˡ-Functor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    Functor (equivalence eqₛ eqₜ) eqₛ (Product.Category S T) S
  πˡ-Functor S T = record
    { signature = πˡ 𝒮 𝒯
    ; structure = πˡ-isFunctor eqₛ eqₜ S T
    }

  πʳ-Homomorphism :
    Homomorphism (equivalence eqₛ eqₜ) eqₜ
  πʳ-Homomorphism = record
    { signature = πʳ 𝒮 𝒯
    ; structure = πʳ-isHomomorphism eqₛ eqₜ
    }

  πʳ-Functor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    Functor (equivalence eqₛ eqₜ) eqₜ (Product.Category S T) T
  πʳ-Functor S T = record
    { signature = πʳ 𝒮 𝒯
    ; structure = πʳ-isFunctor eqₛ eqₜ S T
    }

  Swap-Homomorphism :
    Homomorphism (equivalence eqₛ eqₜ) (equivalence eqₜ eqₛ)
  Swap-Homomorphism = record
    { signature = Swap 𝒮 𝒯
    ; structure = Swap-isHomomorphism eqₛ eqₜ
    }

  Swap-Functor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    Functor (equivalence eqₛ eqₜ) (equivalence eqₜ eqₛ) (Product.Category S T) (Product.Category T S)
  Swap-Functor S T = record
    { signature = Swap 𝒮 𝒯
    ; structure = Swap-isFunctor eqₛ eqₜ S T
    }
