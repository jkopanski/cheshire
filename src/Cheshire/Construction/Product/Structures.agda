{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Product.Structures where

import Data.Product as ×
import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Construction.Product.Signatures as Product

open Product using (𝒬; _※_; _⁂_; assocˡ; assocʳ; πˡ; πʳ; Swap)
open Morphism using (IsHomomorphism; IsFunctor)
open × using (_×_; _,_; <_,_>; proj₁; proj₂)

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    e e′ e″ e‴ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ
    𝒮₁ 𝒯₁ : Quiver o ℓ
    𝒮₂ 𝒯₂ : Quiver o ℓ

equivalence : Equivalence 𝒮 e → Equivalence 𝒯 e′ → Equivalence (𝒬 𝒮 𝒯) (e ⊔ e′)
equivalence S T = record
  { _≈_ = ×.zipWith S._≈_ T._≈_ _×_
  ; equiv = record
    { refl = S.refl , T.refl
    ; sym = ×.map S.sym T.sym
    ; trans = ×.zip S.trans T.trans
    }
  } where module S = Equivalence S
          module T = Equivalence T

IsCategory :
  {S : Category.Signature 𝒮} {T : Category.Signature 𝒯} →
  (isS : Category.Structure e S) (isT : Category.Structure e′ T) →
  Category.Structure (e ⊔ e′) (Product.Category S T)
IsCategory S T = record
  { eq = equivalence S.eq T.eq
  ; assoc = S.assoc , T.assoc
  ; identityˡ = S.identityˡ , T.identityˡ
  ; identityʳ = S.identityʳ , T.identityʳ
  ; ∘-resp-≈ = ×.zip S.∘-resp-≈ T.∘-resp-≈
  } where module S = Category.Structure S
          module T = Category.Structure T

module _
  {eqₛ : Equivalence 𝒮 e} {eqₜ₁ : Equivalence 𝒯₁ e′} {eqₜ₂ : Equivalence 𝒯₂ e″}
  {F : Morphism.t 𝒮 𝒯₁} {G : Morphism.t 𝒮 𝒯₂}
  where

  ※-isHomomorphism :
    (isF : IsHomomorphism F eqₛ eqₜ₁) → (isG : IsHomomorphism G eqₛ eqₜ₂) →
    IsHomomorphism (F ※ G) eqₛ (equivalence eqₜ₁ eqₜ₂)
  ※-isHomomorphism isF isG = record
    { F-resp-≈ = < F.resp-≈ , G.resp-≈ >
    } where module F = IsHomomorphism isF
            module G = IsHomomorphism isG

  ※-isFunctor :
    {S : Category.Signature 𝒮} {T₁ : Category.Signature 𝒯₁} {T₂ : Category.Signature 𝒯₂} →
    (isF : IsFunctor F eqₛ eqₜ₁ S T₁) → (isG : IsFunctor G eqₛ eqₜ₂ S T₂) →
    IsFunctor (F ※ G) eqₛ (equivalence eqₜ₁ eqₜ₂) S (Product.Category T₁ T₂)
  ※-isFunctor isF isG = record
    { isHomomorphism = isHomomorphism
    ; F-resp-id = F.resp-id , G.resp-id
    ; F-resp-∘ = F.resp-∘ , G.resp-∘
    } where module F = IsFunctor isF
            module G = IsFunctor isG
            isHomomorphism = ※-isHomomorphism F.isHomomorphism G.isHomomorphism

module _
  {eqₛ₁ : Equivalence 𝒮₁ e} {eqₛ₂ : Equivalence 𝒮₂ e′} {eqₜ₁ : Equivalence 𝒯₁ e″} {eqₜ₂ : Equivalence 𝒯₂ e‴}
  {F : Morphism.t 𝒮₁ 𝒯₁} {G : Morphism.t 𝒮₂ 𝒯₂}
  where

  ⁂-isHomomorphism :
    (isF : IsHomomorphism F eqₛ₁ eqₜ₁) → (isG : IsHomomorphism G eqₛ₂ eqₜ₂) →
    IsHomomorphism (F ⁂ G) (equivalence eqₛ₁ eqₛ₂) (equivalence eqₜ₁ eqₜ₂)
  ⁂-isHomomorphism isF isG = record
    { F-resp-≈ = ×.map F.resp-≈ G.resp-≈
    } where module F = IsHomomorphism isF
            module G = IsHomomorphism isG

  ⁂-isFunctor :
    {S₁ : Category.Signature 𝒮₁} {S₂ : Category.Signature 𝒮₂} {T₁ : Category.Signature 𝒯₁} {T₂ : Category.Signature 𝒯₂} →
    (isF : IsFunctor F eqₛ₁ eqₜ₁ S₁ T₁) → (isG : IsFunctor G eqₛ₂ eqₜ₂ S₂ T₂) →
    IsFunctor (F ⁂ G) (equivalence eqₛ₁ eqₛ₂) (equivalence eqₜ₁ eqₜ₂) (Product.Category S₁ S₂) (Product.Category T₁ T₂)
  ⁂-isFunctor isF isG = record
    { isHomomorphism = isHomomorphism
    ; F-resp-id = F.resp-id , G.resp-id
    ; F-resp-∘ = F.resp-∘ , G.resp-∘
    } where module F = IsFunctor isF
            module G = IsFunctor isG
            isHomomorphism = ⁂-isHomomorphism F.isHomomorphism G.isHomomorphism

module _
  {C₁ : Quiver o ℓ} {C₂ : Quiver o′ ℓ′} {C₃ : Quiver o″ ℓ″}
  (eq₁ : Equivalence C₁ e) (eq₂ : Equivalence C₂ e′) (eq₃ : Equivalence C₃ e″)
  where

  module eq₁ = Equivalence eq₁
  module eq₂ = Equivalence eq₂
  module eq₃ = Equivalence eq₃

  assocˡ-isHomomorphism :
   IsHomomorphism
     (assocˡ C₁ C₂ C₃)
     (equivalence (equivalence eq₁ eq₂) eq₃)
     (equivalence eq₁ (equivalence eq₂ eq₃))
  assocˡ-isHomomorphism = record
    { F-resp-≈ = < proj₁ ⊙ proj₁ , < proj₂ ⊙ proj₁ , proj₂ > > }

  assocˡ-isFunctor :
    (C₁′ : Category.Signature C₁) (C₂′ : Category.Signature C₂) (C₃′ : Category.Signature C₃) →
    IsFunctor
      (assocˡ C₁ C₂ C₃)
      (equivalence (equivalence eq₁ eq₂) eq₃)
      (equivalence eq₁ (equivalence eq₂ eq₃))
      (Product.Category (Product.Category C₁′ C₂′) C₃′)
      (Product.Category C₁′ (Product.Category C₂′ C₃′))
  assocˡ-isFunctor _ _ _ = record
    { isHomomorphism = assocˡ-isHomomorphism
    ; F-resp-id = eq₁.refl , (eq₂.refl , eq₃.refl)
    ; F-resp-∘ = eq₁.refl , (eq₂.refl , eq₃.refl)
    }

  assocʳ-isHomomorphism :
    IsHomomorphism
      (assocʳ C₁ C₂ C₃)
      (equivalence eq₁ (equivalence eq₂ eq₃))
      (equivalence (equivalence eq₁ eq₂) eq₃)
  assocʳ-isHomomorphism = record
    { F-resp-≈ = < < proj₁ , proj₁ ⊙ proj₂ > , proj₂ ⊙ proj₂ > }

  assocʳ-isFunctor :
    (C₁′ : Category.Signature C₁) (C₂′ : Category.Signature C₂) (C₃′ : Category.Signature C₃) →
    IsFunctor
      (assocʳ C₁ C₂ C₃)
      (equivalence eq₁ (equivalence eq₂ eq₃))
      (equivalence (equivalence eq₁ eq₂) eq₃)
      (Product.Category C₁′ (Product.Category C₂′ C₃′))
      (Product.Category (Product.Category C₁′ C₂′) C₃′)
  assocʳ-isFunctor _ _ _ = record
    { isHomomorphism = assocʳ-isHomomorphism
    ; F-resp-id = (eq₁.refl , eq₂.refl) , eq₃.refl
    ; F-resp-∘ = (eq₁.refl , eq₂.refl) , eq₃.refl
    }

module _ (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′) where

  module eqₛ = Equivalence eqₛ
  module eqₜ = Equivalence eqₜ

  πˡ-isHomomorphism :
    IsHomomorphism (πˡ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₛ
  πˡ-isHomomorphism = record { F-resp-≈ = proj₁ }

  πˡ-isFunctor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    IsFunctor (πˡ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₛ (Product.Category S T) S
  πˡ-isFunctor _ _ = record
    { isHomomorphism = πˡ-isHomomorphism
    ; F-resp-id = eqₛ.refl
    ; F-resp-∘ = eqₛ.refl
    }

  πʳ-isHomomorphism :
    IsHomomorphism (πʳ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₜ
  πʳ-isHomomorphism = record
    { F-resp-≈ = proj₂ }

  πʳ-isFunctor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    IsFunctor (πʳ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₜ (Product.Category S T) T
  πʳ-isFunctor _ _ = record
    { isHomomorphism = πʳ-isHomomorphism
    ; F-resp-id = eqₜ.refl
    ; F-resp-∘ = eqₜ.refl
    }

  Swap-isHomomorphism :
    IsHomomorphism (Swap 𝒮 𝒯) (equivalence eqₛ eqₜ) (equivalence eqₜ eqₛ)
  Swap-isHomomorphism = record { F-resp-≈ = ×.swap }

  Swap-isFunctor :
    (S : Category.Signature 𝒮) (T : Category.Signature 𝒯) →
    IsFunctor
      (Swap 𝒮 𝒯)
      (equivalence eqₛ eqₜ) (equivalence eqₜ eqₛ)
      (Product.Category S T) (Product.Category T S)
  Swap-isFunctor _ _ = record
    { isHomomorphism = Swap-isHomomorphism
    ; F-resp-id = eqₜ.refl , eqₛ.refl
    ; F-resp-∘ = eqₜ.refl , eqₛ.refl
    }
