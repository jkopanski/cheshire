{-# OPTIONS --safe #-}

open import Cheshire.Core
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)

module Cheshire.Construction.Sub.Homomorphism
  {o ℓ e : 𝕃.t} (Underlying : Cartesian.t o ℓ e)
  {i : 𝕃.t} {I : Set i} (H₀ : I → Cartesian.t.𝒬 Underlying .Ob)
  where

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Homomorphism as Homomorphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms
import Cheshire.Prop as Prop

import Cheshire.Construction.Sub.Object as Sub

private
  module U = Cartesian.t Underlying

open Object
open Morphisms.Bundles U.category using (_≅_; Iso)

𝒰 : Quiver o ℓ
𝒰 = U.𝒬

𝒬 : Quiver i ℓ
𝒬 = Sub.𝒬 𝒰 H₀

category : Category.t i ℓ e
category = Sub.Bundles.category (record { Cartesian.t Underlying }) H₀

private
  module H = Homomorphism.t (Sub.H 𝒰 H₀)
  module C = Category.t category

open Morphisms.Reasoning U.isCategory


-- H₀ A -- μ₁ A --→ H₀ A
--   |                |
--   f                f
--   |                |
--   ↓                ↓
-- H₀ B -- μ₁ B --→ H₀ B
R₁ : ((A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) → HomPred 𝒬 e
R₁ μ₁ {A} {B} f = U.CommutativeSquare (μ₁ A) f f (μ₁ B)

P₁ : (μ₁ : (A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) → Prop.Category C.category (R₁ μ₁)
P₁ μ₁ = record
  { id = U.identityˡ ○ (⟺ U.identityʳ)
  ; _∘_ = λ {A B C} {g} {f} gᴿ fᴿ → begin
      (g ∘ f) ∘ μ₁ A ≈⟨ pullʳ fᴿ ⟩
      g ∘ μ₁ B ∘ f   ≈⟨ pullˡ gᴿ ⟩
      (μ₁ C ∘ g) ∘ f ≈⟨ C.assoc  ⟩
      μ₁ C ∘ g ∘ f   ∎
  } where open C using (_∘_)
          open C.HomReasoning


module _
  ⦃ terminalᵢ : Terminal (𝒬 .Ob) ⦄
  ⦃ productsᵢ : BinaryProducts (𝒬 .Ob) ⦄
  (⊤-iso : ⊤ ≅ (H.₀ ⊤))
  (×-iso : ∀ A B → (H.₀ A) × (H.₀ B) ≅ H.₀ (A × B))
  where

  private
    module ⊤-iso = _≅_ ⊤-iso
    module ×-iso {A B} = _≅_ (×-iso A B)

  Sub : Cartesian.t i ℓ e
  Sub = Sub.Bundles.cartesian Underlying H.₀
    (record { _≅_ ⊤-iso } , ⊤-iso.isIso)
    λ A B → record { _≅_ (×-iso A B) } , ×-iso.isIso {A} {B}

  open Cartesian.t Sub hiding (𝒬)

  -- H : Homomorphism.Cartesian′ U.eq (Sub .Cartesian.t.cartesian) U.cartesian
  -- H = Sub.Structures.cartesianFunctor 𝒰 H.₀ U.cartesian U.isCartesian
  --   (record { _≅_ ⊤-iso } , ⊤-iso.isIso)
  --   λ A B → record { _≅_ (×-iso A B) } , ×-iso.isIso {A} {B}

  -- private module F = Homomorphism.Cartesian′ H

  -- H₀ ⊤ -- μ₀ A --→ H₀ A
  --   |                |
  --  id                f
  --   |                |
  --   ↓                ↓
  -- H₀ ⊤ -- μ₀ B --→ H₀ B
  R₀ : ((A : I) → 𝒰 .Hom (H.₀ ⊤) (H.₀ A)) → HomPred 𝒬 e
  R₀ μ₀ {A} {B} f = CommutativeSquare (μ₀ A) U.id f (μ₀ B)

  -- H₀ (A × A) -- μ₁ A --→ H₀ A
  --    |                     |
  --  f ⁂ f                   f
  --    |                     |
  --    ↓                     ↓
  -- H₀ (B × B) -- μ₁ B --→ H₀ B
  R₂ : ((A : I) → 𝒰 .Hom (H.₀ (A × A)) (H.₀ A)) → HomPred 𝒬 e
  R₂ μ₂ {A} {B} f = CommutativeSquare (μ₂ A) (f ⁂ f) f (μ₂ B)

  P₀ : (μ₀ : (A : I) → 𝒰 .Hom (H.₀ ⊤) (H.₀ A)) → Prop.Category C.category (R₀ μ₀)
  P₀ μ₀ = record
    { id = identityˡ ○ (⟺ identityʳ)
    ; _∘_ = λ {A B C} {g} {f} gᴿ fᴿ → begin
        (g ∘ f) ∘ μ₀ A   ≈⟨ pullʳ fᴿ  ⟩
        g ∘ μ₀ B ∘ id    ≈⟨ pullˡ gᴿ  ⟩
        (μ₀ C ∘ id) ∘ id ≈⟨ identityʳ ⟩
        μ₀ C ∘ id        ∎
    }

  P₂ : (μ₂ : (A : I) → 𝒰 .Hom (H.₀ (A × A)) (H.₀ A)) → Prop.Category C.category (R₂ μ₂)
  P₂ μ₂ = record
    { id = λ {A} → begin
       id ∘ μ₂ A          ≈⟨ identityˡ ○ ⟺ identityʳ              ⟩
       μ₂ A ∘ id          ≈⟨ refl⟩∘⟨ η                            ⟨
       μ₂ A ∘ ⟨ π₁ , π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟨
       μ₂ A ∘ (id ⁂ id)   ∎
    ; _∘_ = λ {A B C} {g = g} {f} gᴿ fᴿ → begin
        (g ∘ f) ∘ μ₂ A           ≈⟨ pullʳ fᴿ         ⟩
        g ∘ μ₂ B ∘ (f ⁂ f)       ≈⟨ pullˡ gᴿ ○ assoc ⟩
        μ₂ C ∘ (g ⁂ g) ∘ (f ⁂ f) ≈⟨ refl⟩∘⟨ ⁂∘⁂      ⟩
        μ₂ C ∘ (g ∘ f ⁂ g ∘ f)   ∎
    }

  P₀× :
    (μ₀ : (A : I) → 𝒰 .Hom (H.₀ ⊤) (H.₀ A)) →
    (∀ {A B : I} → μ₀ (A × B) U.≈ ⟨ μ₀ A , μ₀ B ⟩) →
    Prop.Cartesian cartesian (R₀ μ₀)
  P₀× μ₀ μₓ = record
    { category = P₀ μ₀
    ; ! = !-unique₂
    ; π₁ = λ {A B} → begin
        π₁ ∘ μ₀ (A × B)      ≈⟨ refl⟩∘⟨ μₓ ⟩
        π₁ ∘ ⟨ μ₀ A , μ₀ B ⟩ ≈⟨ project₁   ⟩
        μ₀ A                 ≈⟨ identityʳ  ⟨
        μ₀ A ∘ C.id          ∎
    ; π₂ = λ {A B} → begin
        π₂ ∘ μ₀ (A × B)      ≈⟨ refl⟩∘⟨ μₓ ⟩
        π₂ ∘ ⟨ μ₀ A , μ₀ B ⟩ ≈⟨ project₂   ⟩
        μ₀ B                 ≈⟨ identityʳ  ⟨
        μ₀ B ∘ C.id           ∎
    ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
        ⟨ f , g ⟩ ∘ μ₀ C        ≈⟨ ∘-distribʳ-⟨⟩                              ⟩
        ⟨ f ∘ μ₀ C , g ∘ μ₀ C ⟩ ≈⟨ ⟨⟩-cong₂ (fᴿ ○ identityʳ) (gᴿ ○ identityʳ) ⟩
        ⟨ μ₀ A , μ₀ B ⟩         ≈⟨ ⟺ μₓ ○ ⟺ U.identityʳ                       ⟩
        μ₀ (A × B) ∘ id         ∎
    }

  P₁× :
    (μ₁ : (A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) →
    (∀ {A B : I} → μ₁ (A × B) U.≈ μ₁ A ⁂ μ₁ B) →
    Prop.Cartesian cartesian (R₁ μ₁)
  P₁× μ₁ μ× = record
    { category = P₁ μ₁
    ; ! = !-unique₂
    ; π₁ = λ {A B} → begin
        π₁ ∘ μ₁ (A × B)    ≈⟨ refl⟩∘⟨ μ× ⟩
        π₁ ∘ (μ₁ A ⁂ μ₁ B) ≈⟨ π₁∘⁂       ⟩
        μ₁ A ∘ π₁          ∎
    ; π₂ = λ {A B} → begin
        π₂ ∘ μ₁ (A × B)    ≈⟨ refl⟩∘⟨ μ× ⟩
        π₂ ∘ (μ₁ A ⁂ μ₁ B) ≈⟨ π₂∘⁂       ⟩
        μ₁ B ∘ π₂          ∎
    ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
        ⟨ f , g ⟩ ∘ μ₁ C          ≈⟨ ∘-distribʳ-⟨⟩  ⟩
        ⟨ f ∘ μ₁ C , g ∘ μ₁ C ⟩   ≈⟨ ⟨⟩-cong₂ fᴿ gᴿ ⟩
        ⟨ μ₁ A ∘ f , μ₁ B ∘ g ⟩   ≈⟨ ⁂∘⟨⟩           ⟨
        (μ₁ A ⁂ μ₁ B) ∘ ⟨ f , g ⟩ ≈⟨ μ× ⟩∘⟨refl     ⟨
        μ₁ (A × B) ∘ ⟨ f , g ⟩        ∎
    }

  -- -- TODO: This is "four middle interchange", from:
  -- -- https://agda.github.io/agda-categories/Categories.Category.Monoidal.Interchange.html
  -- interchange :
  --   ∀ {A B C D} →
  --   𝒬 .Hom ((A × B) × (C × D)) ((A × C) × (B × D))
  -- interchange =
  --   ⟨ ⟨ π₁ ∘ π₁ , π₁ ∘ π₂ ⟩
  --   , ⟨ π₂ ∘ π₁ , π₂ ∘ π₂ ⟩
  --   ⟩
  -- -- U.⟨ U.⟨ U.π₁ U.∘ U.π₁ , U.π₁ U.∘ U.π₂ ⟩
  -- --   , U.⟨ U.π₂ U.∘ U.π₁ , U.π₂ U.∘ U.π₂ ⟩
  -- --   ⟩

  P₂× :
    (μ₂ : (A : I) → 𝒰 .Hom (H.₀ (A × A)) (H.₀ A)) →
    (∀ {A B : I} → μ₂ (A × B) U.≈ (μ₂ A ⁂ μ₂ B) ∘ interchange) →
    Prop.Cartesian cartesian (R₂ μ₂)
  P₂× μ₂ μ× = record
    { category = P₂ μ₂
    ; ! = !-unique₂
    ; π₁ = λ {A B} → begin
        π₁ ∘ μ₂ (A × B)                  ≈⟨ refl⟩∘⟨ μ×         ⟩
        π₁ ∘ (μ₂ A ⁂ μ₂ B) ∘ interchange ≈⟨ pullˡ π₁∘⁂ ○ assoc ⟩
        μ₂ A ∘ π₁ ∘ interchange          ≈⟨ refl⟩∘⟨ project₁   ⟩
        μ₂ A ∘ (π₁ ⁂ π₁)                 ∎
    ; π₂ = λ {A B} → begin
        π₂ ∘ μ₂ (A × B)                  ≈⟨ refl⟩∘⟨ μ×         ⟩
        π₂ ∘ (μ₂ A ⁂ μ₂ B) ∘ interchange ≈⟨ pullˡ π₂∘⁂ ○ assoc ⟩
        μ₂ B ∘ π₂ ∘ interchange          ≈⟨ refl⟩∘⟨ project₂   ⟩
        μ₂ B ∘ (π₂ ⁂ π₂)                 ∎
    ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
        ⟨ f , g ⟩ ∘ μ₂ C                                      ≈⟨ ∘-distribʳ-⟨⟩      ⟩
        ⟨ f ∘ μ₂ C  , g ∘ μ₂ C  ⟩                             ≈⟨ ⟨⟩-cong₂ fᴿ gᴿ     ⟩
        ⟨ μ₂ A ∘ (f ⁂ f) , μ₂ B ∘ (g ⁂ g)  ⟩                  ≈⟨ ⁂∘⟨⟩               ⟨
        (μ₂ A ⁂ μ₂ B) ∘ ⟨ f ⁂ f , g ⁂ g ⟩                     ≈⟨ refl⟩∘⟨ weave      ⟩
        (μ₂ A ⁂ μ₂ B) ∘ interchange ∘ (⟨ f , g ⟩ ⁂ ⟨ f , g ⟩) ≈⟨ μ× ⟩∘⟨refl ○ assoc ⟨
        μ₂ (A × B) ∘ (⟨ f , g ⟩ ⁂ ⟨ f , g ⟩) ∎
   } where
       weave :
         ∀ {X A B C D} →
         ∀ {p : 𝒬 .Hom X A} {q : 𝒬 .Hom X B} {r : 𝒬 .Hom X C} {s : 𝒬 .Hom X D} →
         ⟨ p ⁂ q , r ⁂ s ⟩ U.≈ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
       weave {p = p} {q} {r} {s} = unique left right
         where left : π₁ ∘ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩) U.≈ p ⁂ q
               left = begin
                   π₁ ∘ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                 ≈⟨ pullˡ project₁ ⟩
                   ⟨ π₁ ∘ π₁ , π₁ ∘ π₂ ⟩ ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                 ≈⟨ ∘-distribʳ-⟨⟩ ⟩
                   ⟨ (π₁ ∘ π₁) ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                   , (π₁ ∘ π₂) ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                   ⟩
                 ≈⟨ ⟨⟩-cong₂
                      (pullʳ π₁∘⁂ ○ pullˡ project₁)
                      (pullʳ π₂∘⁂ ○ pullˡ project₁) ⟩
                   p ⁂ q
                 ∎
               right : π₂ ∘ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩) U.≈ r ⁂ s
               right = begin
                   π₂ ∘ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                 ≈⟨ pullˡ project₂ ⟩
                   ⟨ π₂ ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                 ≈⟨ ∘-distribʳ-⟨⟩ ⟩
                   ⟨ (π₂ ∘ π₁) ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                   , (π₂ ∘ π₂) ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
                   ⟩
                 ≈⟨ ⟨⟩-cong₂
                      (pullʳ π₁∘⁂ ○ pullˡ project₂)
                      (pullʳ π₂∘⁂ ○ pullˡ project₂) ⟩
                   r ⁂ s
                 ∎
