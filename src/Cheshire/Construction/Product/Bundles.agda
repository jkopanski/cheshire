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
  (S : Category.t o ℓ e) (T : Category.t o′ ℓ′ e′) →
  Category.t (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Category S T = record
  { 𝒬          = 𝒬 S.𝒬 T.𝒬
  ; category   = Product.Category S.category T.category
  ; isCategory = IsCategory S.isCategory T.isCategory
  } where module S = Category.t S
          module T = Category.t T

module _
  ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ₁ : Equivalence 𝒯₁ e′ ⦄ ⦃ eqₜ₂ : Equivalence 𝒯₂ e″ ⦄
  where

  ※-Homomorphism :
    (F : Homomorphism 𝒮 𝒯₁) (G : Homomorphism 𝒮 𝒯₂) →
    Homomorphism 𝒮 (𝒬 𝒯₁ 𝒯₂) ⦃ _ ⦄ ⦃ equivalence eqₜ₁ eqₜ₂ ⦄
  ※-Homomorphism F G = record
    { morphism = F.morphism ※ G.morphism
    ; isHomomorphism = ※-isHomomorphism F.isHomomorphism G.isHomomorphism
    } where module F = Homomorphism F
            module G = Homomorphism G

  ※-Functor :
    {S : Category.Signature 𝒮} {T₁ : Category.Signature 𝒯₁} {T₂ : Category.Signature 𝒯₂} →
    (F : Functor S T₁) (G : Functor S T₂) →
    Functor ⦃ eqₜ = equivalence eqₜ₁ eqₜ₂ ⦄ S (Product.Category T₁ T₂)
  ※-Functor F G = record
    { morphism = F.morphism ※ G.morphism
    ; isFunctor = ※-isFunctor F.isFunctor G.isFunctor
    ; isHomomorphism = ※-isHomomorphism F.isHomomorphism G.isHomomorphism
    } where module F = Functor F
            module G = Functor G

module _
  ⦃ eqₛ₁ : Equivalence 𝒮₁ e ⦄ ⦃ eqₛ₂ : Equivalence 𝒮₂ e′ ⦄ ⦃ eqₜ₁ : Equivalence 𝒯₁ e″ ⦄ ⦃ eqₜ₂ : Equivalence 𝒯₂ e‴ ⦄
  where

  ⁂-Homomorphism :
    (F : Homomorphism 𝒮₁ 𝒯₁) (G : Homomorphism 𝒮₂ 𝒯₂) →
    Homomorphism (𝒬 𝒮₁ 𝒮₂) (𝒬 𝒯₁ 𝒯₂) ⦃ equivalence eqₛ₁ eqₛ₂ ⦄ ⦃ equivalence eqₜ₁ eqₜ₂ ⦄
  ⁂-Homomorphism F G = record
    { morphism = F.morphism ⁂ G.morphism
    ; isHomomorphism = ⁂-isHomomorphism F.isHomomorphism G.isHomomorphism
    } where module F = Homomorphism F
            module G = Homomorphism G

  ⁂-Functor :
    {S₁ : Category.Signature 𝒮₁} {S₂ : Category.Signature 𝒮₂} {T₁ : Category.Signature 𝒯₁} {T₂ : Category.Signature 𝒯₂} →
    (F : Functor S₁ T₁) (G : Functor S₂ T₂) →
    Functor
      ⦃ equivalence eqₛ₁ eqₛ₂ ⦄ ⦃ equivalence eqₜ₁ eqₜ₂ ⦄
      (Product.Category S₁ S₂) (Product.Category T₁ T₂)
  ⁂-Functor F G = record
    { morphism = F.morphism ⁂ G.morphism
    ; isFunctor = ⁂-isFunctor F.isFunctor G.isFunctor
    ; isHomomorphism = ⁂-isHomomorphism F.isHomomorphism G.isHomomorphism
    } where module F = Functor F
            module G = Functor G

module _
  {C₁ : Quiver o ℓ} {C₂ : Quiver o′ ℓ′} {C₃ : Quiver o″ ℓ″}
  ⦃ eq₁ : Equivalence C₁ e ⦄ ⦃ eq₂ : Equivalence C₂ e′ ⦄ ⦃ eq₃ : Equivalence C₃ e″ ⦄
  where

  assocˡ-Homomorphism : Homomorphism (𝒬 (𝒬 C₁ C₂) C₃) (𝒬 C₁ (𝒬 C₂ C₃))
  assocˡ-Homomorphism = record
    { morphism = assocˡ C₁ C₂ C₃
    ; isHomomorphism = assocˡ-isHomomorphism
    }

  assocˡ-Functor :
    (C₁′ : Category.Signature C₁) (C₂′ : Category.Signature C₂) (C₃′ : Category.Signature C₃) →
    Functor
      (Product.Category (Product.Category C₁′ C₂′) C₃′)
      (Product.Category C₁′ (Product.Category C₂′ C₃′))
  assocˡ-Functor C₁′ C₂′ C₃′ = record
    { morphism = assocˡ C₁ C₂ C₃
    ; isFunctor = assocˡ-isFunctor C₁′ C₂′ C₃′
    ; isHomomorphism = assocˡ-isHomomorphism
    }

  assocʳ-Homomorphism :
    Homomorphism
      (𝒬 C₁ (𝒬 C₂ C₃))
      (𝒬 (𝒬 C₁ C₂) C₃)
  assocʳ-Homomorphism = record
    { morphism = assocʳ C₁ C₂ C₃
    ; isHomomorphism = assocʳ-isHomomorphism
    }

  assocʳ-Functor :
    (C₁′ : Category.Signature C₁) (C₂′ : Category.Signature C₂) (C₃′ : Category.Signature C₃) →
    Functor
      (Product.Category C₁′ (Product.Category C₂′ C₃′))
      (Product.Category (Product.Category C₁′ C₂′) C₃′)
  assocʳ-Functor C₁′ C₂′ C₃′ = record
    { morphism = assocʳ C₁ C₂ C₃
    ; isFunctor = assocʳ-isFunctor C₁′ C₂′ C₃′
    ; isHomomorphism = assocʳ-isHomomorphism
    }

module _ ⦃ eqₛ : Equivalence 𝒮 e ⦄ ⦃ eqₜ : Equivalence 𝒯 e′ ⦄ where

  πˡ-Homomorphism : Homomorphism (𝒬 𝒮 𝒯) 𝒮
  πˡ-Homomorphism = record
    { morphism = πˡ 𝒮 𝒯
    ; isHomomorphism = πˡ-isHomomorphism
    }

  πˡ-Functor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    Functor (Product.Category S T) S
  πˡ-Functor S T = record
    { morphism = πˡ 𝒮 𝒯
    ; isFunctor = πˡ-isFunctor S T
    ; isHomomorphism = πˡ-isHomomorphism
    }

  πʳ-Homomorphism : Homomorphism (𝒬 𝒮 𝒯) 𝒯
  πʳ-Homomorphism = record
    { morphism = πʳ 𝒮 𝒯
    ; isHomomorphism = πʳ-isHomomorphism
    }

  πʳ-Functor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    Functor (Product.Category S T) T
  πʳ-Functor S T = record
    { morphism = πʳ 𝒮 𝒯
    ; isFunctor = πʳ-isFunctor S T
    ; isHomomorphism = πʳ-isHomomorphism
    }

  Swap-Homomorphism : Homomorphism (𝒬 𝒮 𝒯) (𝒬 𝒯 𝒮)
  Swap-Homomorphism = record
    { morphism = Swap 𝒮 𝒯
    ; isHomomorphism = Swap-isHomomorphism
    }

  Swap-Functor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    Functor (Product.Category S T) (Product.Category T S)
  Swap-Functor S T = record
    { morphism = Swap 𝒮 𝒯
    ; isFunctor = Swap-isFunctor S T
    ; isHomomorphism = Swap-isHomomorphism
    }
