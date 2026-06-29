{-# OPTIONS --safe #-}

-- This module probably doesn't belong in this project

open import Cheshire.Core
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Homomorphism as Homomorphism renaming (Morphism to t)

module Cheshire.Construction.Sub.Algebraic
  {o ℓ e : 𝕃.t} (Underlying : Cartesian.t o ℓ e)
  (let module Underlying = Cartesian.t Underlying)
  {i} {I : Set i} (F₀ : I → Underlying.𝒬 .Ob)
  where

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Homomorphism as Homomorphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms
import Cheshire.Prop as Prop

import Cheshire.Construction.Sub.Object as Subₒ
import Cheshire.Construction.Sub.Morphism as Subₘ

open Homomorphism using (_≃_)
open Object
open Morphisms.Bundles Underlying.category using (_≅_)

--   A ---------- f , R f --------------→ B
--   |              ∥                     |
--   id           proj₁                   id
--   |              ∥                     |
--   ↓              ⇓                     ↓
--   A --- f : 𝒰 .Hom (F₀ A) (F₀ B) ----→ B
--   |              ∥                     |
--   F₀             id                    F₀
--   |              ∥                     |
--   ↓              ⇓                     ↓
-- F₀ A -- f : 𝒰 .Hom (F₀ A) (F₀ B) --→ F₀ B

ℐ : Quiver i ℓ
ℐ = mk⇒ λ A B → Underlying.𝒬 .Hom (F₀ A) (F₀ B)

module Intermediate where
  𝒬 : Quiver i ℓ
  𝒬 = Subₒ.𝒬 Underlying.𝒬 F₀

  -- sanity check
  _ : ℐ ≡ 𝒬
  _ = ≡-refl

  category : Category.t i ℓ e
  category = Subₒ.Bundles.category (record { Cartesian.t Underlying }) F₀

  H : Homomorphism.t 𝒬 Underlying.𝒬
  H = Subₒ.H Underlying.𝒬 F₀

  module _
    ⦃ _ : Terminal I ⦄ ⦃ _ : BinaryProducts I ⦄
    (⊤-iso : ⊤ ≅ F₀ ⊤)
    (×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B))
    where

    cartesian : Cartesian.t i ℓ e
    cartesian = Subₒ.Bundles.cartesian Underlying F₀ ⊤-iso ×-iso

module _
  ⦃ _ : Terminal I ⦄ ⦃ _ : BinaryProducts I ⦄
  (⊤-iso : ⊤ ≅ F₀ ⊤)
  (×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B))
  where

  I× = Intermediate.cartesian ⊤-iso ×-iso
  module I = Cartesian.t I×
  open I hiding (category; cartesian)
  open I.Reasoning

  module Op₀ (μ : ∀ (A : I) → ℐ .Hom ⊤ A) where

    R : HomPred ℐ e
    R {A} {B} f = CommutativeSquare (μ A) I.id f (μ B)

    P : Prop.Category.t I.category R
    P = record
      { id = identityˡ ○ (⟺ identityʳ)
      ; _∘_ = λ {A B C} {g} {f} gᴿ fᴿ → begin
          (g ∘ f) ∘ μ A   ≈⟨ pullʳ fᴿ  ⟩
          g ∘ μ B ∘ id    ≈⟨ pullˡ gᴿ  ⟩
          (μ C ∘ id) ∘ id ≈⟨ identityʳ ⟩
          μ C ∘ id        ∎
      }

    category : Category.t i (ℓ ⊔ e) e
    category = Subₘ.Bundles.category (record { Cartesian.t I× }) R P

    module _ (μ× : ∀ {A B : I} → μ (A × B) I.≈ ⟨ μ A , μ B ⟩) where

      P× : Prop.Cartesian.t I.cartesian R
      P× = record
        { ! = !-unique₂
        ; π₁ = λ {A B} → begin
            π₁ ∘ μ (A × B)     ≈⟨ refl⟩∘⟨ μ× ⟩
            π₁ ∘ ⟨ μ A , μ B ⟩ ≈⟨ project₁   ⟩
            μ A                ≈⟨ identityʳ  ⟨
            μ A ∘ id           ∎
        ; π₂ = λ {A B} → begin
            π₂ ∘ μ (A × B)     ≈⟨ refl⟩∘⟨ μ× ⟩
            π₂ ∘ ⟨ μ A , μ B ⟩ ≈⟨ project₂   ⟩
            μ B                ≈⟨ identityʳ  ⟨
            μ B ∘ id           ∎
        ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
            ⟨ f , g ⟩ ∘ μ C       ≈⟨ ∘-distribʳ-⟨⟩                              ⟩
            ⟨ f ∘ μ C , g ∘ μ C ⟩ ≈⟨ ⟨⟩-cong₂ (fᴿ ○ identityʳ) (gᴿ ○ identityʳ) ⟩
            ⟨ μ A , μ B ⟩         ≈⟨ ⟺ μ× ○ ⟺ identityʳ                         ⟩
            μ (A × B) ∘ id        ∎
        }

      cartesian : Cartesian.t i (ℓ ⊔ e) e
      cartesian = Subₘ.Bundles.cartesian I× P P×

  module Op₁ (μ : ∀ (A : I) → ℐ .Hom A A) where

    R : HomPred ℐ e
    R {A} {B} f = CommutativeSquare (μ A) f f (μ B)

    P : Prop.Category.t I.category R
    P = record
      { id = identityˡ ○ (⟺ identityʳ)
      ; _∘_ = λ {A B C} {g} {f} gᴿ fᴿ → begin
          (g ∘ f) ∘ μ A ≈⟨ pullʳ fᴿ  ⟩
          g ∘ μ B ∘ f   ≈⟨ pullˡ gᴿ  ⟩
          (μ C ∘ g) ∘ f ≈⟨ assoc ⟩
          μ C ∘ g ∘ f   ∎
      }

    category : Category.t i (ℓ ⊔ e) e
    category = Subₘ.Bundles.category (record { Cartesian.t I× }) R P

    module _ (μ× : ∀ {A B : I} → μ (A × B) I.≈ μ A ⁂ μ B) where

      P× : Prop.Cartesian.t I.cartesian R
      P× = record
        { ! = !-unique₂
        ; π₁ = λ {A B} → begin
            π₁ ∘ μ (A × B)   ≈⟨ refl⟩∘⟨ μ× ⟩
            π₁ ∘ (μ A ⁂ μ B) ≈⟨ π₁∘⁂       ⟩
            μ A ∘ π₁         ∎
        ; π₂ = λ {A B} → begin
            π₂ ∘ μ (A × B)   ≈⟨ refl⟩∘⟨ μ× ⟩
            π₂ ∘ (μ A ⁂ μ B) ≈⟨ π₂∘⁂       ⟩
            μ B ∘ π₂         ∎
        ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
            ⟨ f , g ⟩ ∘ μ C         ≈⟨ ∘-distribʳ-⟨⟩  ⟩
            ⟨ f ∘ μ C , g ∘ μ C ⟩   ≈⟨ ⟨⟩-cong₂ fᴿ gᴿ ⟩
            ⟨ μ A ∘ f , μ B ∘ g ⟩   ≈⟨ ⁂∘⟨⟩           ⟨
            (μ A ⁂ μ B) ∘ ⟨ f , g ⟩ ≈⟨ μ× ⟩∘⟨refl     ⟨
            μ (A × B) ∘ ⟨ f , g ⟩   ∎
        }

      cartesian : Cartesian.t i (ℓ ⊔ e) e
      cartesian = Subₘ.Bundles.cartesian I× P P×

  module Op₂ (μ : ∀ (A : I) → ℐ .Hom (A × A) A) where

    R : HomPred ℐ e
    R {A} {B} f = CommutativeSquare (μ A) (f ⁂ f) f (μ B)

    P : Prop.Category.t I.category R
    P = record
      { id = λ {A} → begin
          id ∘ μ A          ≈⟨ identityˡ ○ ⟺ identityʳ              ⟩
          μ A ∘ id          ≈⟨ refl⟩∘⟨ η                            ⟨
          μ A ∘ ⟨ π₁ , π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟨
          μ A ∘ (id ⁂ id)   ∎
      ; _∘_ = λ {A B C} {g = g} {f} gᴿ fᴿ → begin
          (g ∘ f) ∘ μ A           ≈⟨ pullʳ fᴿ         ⟩
          g ∘ μ B ∘ (f ⁂ f)       ≈⟨ pullˡ gᴿ ○ assoc ⟩
          μ C ∘ (g ⁂ g) ∘ (f ⁂ f) ≈⟨ refl⟩∘⟨ ⁂∘⁂      ⟩
          μ C ∘ (g ∘ f ⁂ g ∘ f)   ∎
      }

    category : Category.t i (ℓ ⊔ e) e
    category = Subₘ.Bundles.category (record { Cartesian.t I× }) R P

    module _ (μ× : ∀ {A B : I} → μ (A × B) I.≈ (μ A ⁂ μ B) ∘ interchange) where

      P× : Prop.Cartesian.t I.cartesian R
      P× = record
        { ! = !-unique₂
        ; π₁ = λ {A B} → begin
            π₁ ∘ μ (A × B)                 ≈⟨ refl⟩∘⟨ μ×         ⟩
            π₁ ∘ (μ A ⁂ μ B) ∘ interchange ≈⟨ pullˡ π₁∘⁂ ○ assoc ⟩
            μ A ∘ π₁ ∘ interchange         ≈⟨ refl⟩∘⟨ project₁   ⟩
            μ A ∘ (π₁ ⁂ π₁)                ∎
        ; π₂ = λ {A B} → begin
            π₂ ∘ μ (A × B)                 ≈⟨ refl⟩∘⟨ μ×         ⟩
            π₂ ∘ (μ A ⁂ μ B) ∘ interchange ≈⟨ pullˡ π₂∘⁂ ○ assoc ⟩
            μ B ∘ π₂ ∘ interchange         ≈⟨ refl⟩∘⟨ project₂   ⟩
            μ B ∘ (π₂ ⁂ π₂)                ∎
        ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
            ⟨ f , g ⟩ ∘ μ C                                     ≈⟨ ∘-distribʳ-⟨⟩      ⟩
            ⟨ f ∘ μ C  , g ∘ μ C  ⟩                             ≈⟨ ⟨⟩-cong₂ fᴿ gᴿ     ⟩
            ⟨ μ A ∘ (f ⁂ f) , μ B ∘ (g ⁂ g)  ⟩                  ≈⟨ ⁂∘⟨⟩               ⟨
            (μ A ⁂ μ B) ∘ ⟨ f ⁂ f , g ⁂ g ⟩                     ≈⟨ refl⟩∘⟨ weave      ⟩
            (μ A ⁂ μ B) ∘ interchange ∘ (⟨ f , g ⟩ ⁂ ⟨ f , g ⟩) ≈⟨ μ× ⟩∘⟨refl ○ assoc ⟨
            μ (A × B) ∘ (⟨ f , g ⟩ ⁂ ⟨ f , g ⟩)                 ∎
        } where
          weave :
            ∀ {X A B C D} →
            ∀ {p : 𝒬 .Hom X A} {q : 𝒬 .Hom X B} {r : 𝒬 .Hom X C} {s : 𝒬 .Hom X D} →
            ⟨ p ⁂ q , r ⁂ s ⟩ I.≈ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩)
          weave {p = p} {q} {r} {s} = unique left right
            where left : π₁ ∘ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩) I.≈ p ⁂ q
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
                  right : π₂ ∘ interchange ∘ (⟨ p , r ⟩ ⁂ ⟨ q , s ⟩) I.≈ r ⁂ s
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

      cartesian : Cartesian.t i (ℓ ⊔ e) e
      cartesian = Subₘ.Bundles.cartesian I× P P×
