{-# OPTIONS --safe #-}

open import Overture using (module ×)
open import Cheshire.Core
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)

module Cheshire.Instance.Algebraic
  {o ℓ e : 𝕃.t} (Underlying : Cartesian.t o ℓ e)
  {i : 𝕃.t} {I : Set i} (H₀ : I → Cartesian.t.𝒬 Underlying .Ob)
  where

import Algebra.Morphism.Definitions as Definitions
import Relation.Binary.Reasoning.MultiSetoid as Multi

import Relation.Binary.Indexed.Homogeneous.Bundles as IndexedSetoid renaming (IndexedSetoid to t)
import Relation.Binary.Indexed.Homogeneous.Construct.At as At

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Homomorphism as Homomorphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Prop as Prop
import Cheshire.Morphism as Morphisms
import Cheshire.Morphism.Reasoning.Iso as IsoReasoning
import Cheshire.Construction.Sub.Object as Subₒ
import Cheshire.Construction.Sub.Morphism as Subₘ
-- import Cheshire.Instance.Setoids o as Setoids renaming (Setoids to t)
-- import Cheshire.Instance.Sets o as Sets renaming (Sets to t)

open import Algebra.Core using (Op₁; Op₂)
-- open import Data.Product.Base using (Σ-syntax)
-- open import Data.Product.Relation.Binary.Pointwise.NonDependent
--   using (Pointwise; ×-isEquivalence; ×-refl)
-- open import Relation.Binary.Definitions
--   using (Substitutive)
-- open import Relation.Binary.Morphism.Structures
--   using (IsRelHomomorphism; IsRelMonomorphism; IsRelIsomorphism)

module Algebra where
  open import Algebra.Bundles public
  open import Algebra.Module.Bundles public
  module Terminal where
    open import Algebra.Construct.Terminal public

private
  module U = Cartesian.t Underlying

open Category using (_[_∘_])
open Object
open Prop using (HomPred)
open Morphisms.Structures.IsIso
open Morphisms.Bundles U.category using (_≅_; Iso)

𝒰 : Quiver o ℓ
𝒰 = U.𝒬

𝒬 : Quiver i ℓ
𝒬 = Subₒ.𝒬 𝒰 H₀
-- 𝒬 = mk⇒ λ a b → Setoids.𝒬 [ H₀ a , H₀ b ]

instance eq = Subₒ.Structures.eq 𝒰 H₀

H : Homomorphism.t 𝒬 𝒰
H = Subₒ.H 𝒰 H₀

category : Category.t i ℓ e
category = Subₒ.Bundles.category (record { Cartesian.t Underlying }) H₀

F : Homomorphism.Functor′ U.eq (record { Category.t category }) U.category
F = Subₒ.Structures.functor 𝒰 H₀ U.category

private
  module H = Homomorphism.t H
  module C = Category.t category

open U using (_∘_)
open Morphisms.Reasoning U.isCategory

--   -- ⊤ -- μ₀ A --> A
--   -- |             |
--   -- id            f
--   -- |             |
--   -- V             V
--   -- ⊤ -- μ₀ B --> B
--   -- R₀ :
--   --   ⦃ _ : Terminal (𝒬 .Ob) ⦄ →
--   --   -- is the ⊤ right here? Should I use H.₀ ⊤? Then I would need
--   --   -- bunch of other stuff + more complicated commutation?
--   --   ((A : I) → Setoids.𝒬 .Hom (H.₀ ⊤) (H.₀ A)) → HomPred 𝒬 o
--   -- R₀ μ₀ {A} {B} f = CommutativeSquare (μ₀ A) S.id f (μ₀ B)

-- A -- μ₁ A --> ?
-- |             |
-- f             f
-- |             |
-- V             V
-- B -- μ₁ B --> ?
R₁ : ((A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) → HomPred 𝒬 e
R₁ μ₁ {A} {B} f = U.CommutativeSquare (μ₁ A) f f (μ₁ B)


-- R₂ : ((A : I) → 𝒰 .Hom (H.₀ A × H.₀ A) (H.₀ A)) → HomPred 𝒬 e
-- R₂ μ₂ {A} {B} f = U.CommutativeSquare (μ₂ A) (f U.⁂ f) f (μ₂ B)

-- --   -- P₀ : ⦃ _ : Terminal (𝒬 .Ob) ⦄ → (μ₀ : (A : I) → Setoids.𝒬 .Hom (H.₀ ⊤) (H.₀ A)) → Prop.Category 𝒞 (R₀ μ₀)
-- --   -- P₀ μ₀ = record
-- --   --   { id = λ _ → reflᵢ
-- --   --   ; _∘_ = λ {g = g} {f} gᴿ fᴿ → λ x → transᵢ (g .cong (fᴿ x)) (gᴿ x)
-- --   --   }

P₁ : (μ₁ : (A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) → Prop.Category C.category (R₁ μ₁)
P₁ μ₁ = record
  { id = U.identityˡ ○ (⟺ U.identityʳ)
  ; _∘_ = λ {A B C} {g = g} {f} gᴿ fᴿ → begin
      (g ∘ f) ∘ μ₁ A ≈⟨ pullʳ fᴿ ⟩
      g ∘ μ₁ B ∘ f   ≈⟨ pullˡ gᴿ ⟩
      (μ₁ C ∘ g) ∘ f ≈⟨ U.assoc  ⟩
      μ₁ C ∘ g ∘ f   ∎
  } where open U.HomReasoning

-- P₂ : (μ₂ : (A : I) → 𝒰 .Hom (H.₀ A × H.₀ A) (H.₀ A)) → Prop.Category C.category (R₂ μ₂)
-- P₂ μ₂ = record
--   { id = λ {A} → begin
--       U.id ∘ μ₂ A              ≈⟨ U.identityˡ ○ ⟺ U.identityʳ ⟩
--       μ₂ A ∘ U.id              ≈⟨ refl⟩∘⟨ U.η ⟨
--       μ₂ A ∘ U.⟨ U.π₁ , U.π₂ ⟩ ≈⟨ refl⟩∘⟨ U.⟨⟩-cong₂ U.identityˡ U.identityˡ ⟨
--       μ₂ A ∘ (U.id U.⁂ U.id)   ∎
--   ; _∘_ = λ {A B C} {g = g} {f} gᴿ fᴿ → begin
--       (g ∘ f) ∘ μ₂ A               ≈⟨ pullʳ fᴿ           ⟩
--       g ∘ μ₂ B ∘ (f U.⁂ f)         ≈⟨ pullˡ gᴿ ○ U.assoc ⟩
--       μ₂ C ∘ (g U.⁂ g) ∘ (f U.⁂ f) ≈⟨ refl⟩∘⟨ U.⁂∘⁂      ⟩
--       μ₂ C ∘ (g ∘ f U.⁂ g ∘ f)     ∎
--   } where open U.HomReasoning

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
  Sub = Subₒ.Bundles.cartesian Underlying H.₀
    (record { _≅_ ⊤-iso } , ⊤-iso.isIso)
    λ A B → record { _≅_ (×-iso A B) } , ×-iso.isIso {A} {B}
  private
    module Sub = Cartesian.t Sub

  ℋ : Homomorphism.Cartesian′ U.eq (Sub.cartesian) U.cartesian
  ℋ = Subₒ.Structures.cartesianFunctor 𝒰 H.₀ U.cartesian U.isCartesian
    (record { _≅_ ⊤-iso } , ⊤-iso.isIso)
    λ A B → record { _≅_ (×-iso A B) } , ×-iso.isIso {A} {B}

  private module F = Homomorphism.Cartesian′ ℋ

  P₁× :
    (μ₁ : (A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) →
    (∀ {A B : I} → μ₁ (A × B) U.≈ μ₁ A Sub.⁂ μ₁ B) →
    Prop.Cartesian Sub.cartesian (R₁ μ₁)
  P₁× μ₁ μ× = record
    { ! = Sub.!-unique₂
    ; π₁ = λ {A B} → begin
        Sub.π₁ ∘ μ₁ (A × B)        ≈⟨ refl⟩∘⟨ μ× ⟩
        Sub.π₁ ∘ (μ₁ A Sub.⁂ μ₁ B) ≈⟨ Sub.π₁∘⁂   ⟩
        μ₁ A ∘ Sub.π₁              ∎
    ; π₂ = λ {A B} → begin
        Sub.π₂ ∘ μ₁ (A × B)        ≈⟨ refl⟩∘⟨ μ× ⟩
        Sub.π₂ ∘ (μ₁ A Sub.⁂ μ₁ B) ≈⟨ Sub.π₂∘⁂   ⟩
        μ₁ B ∘ Sub.π₂              ∎
    ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → begin
        Sub.⟨ f , g ⟩ ∘ μ₁ C              ≈⟨ Sub.∘-distribʳ-⟨⟩  ⟩
        Sub.⟨ f ∘ μ₁ C , g ∘ μ₁ C ⟩       ≈⟨ Sub.⟨⟩-cong₂ fᴿ gᴿ ⟩
        Sub.⟨ μ₁ A ∘ f , μ₁ B ∘ g ⟩       ≈⟨ Sub.⁂∘⟨⟩           ⟨
        (μ₁ A Sub.⁂ μ₁ B) ∘ Sub.⟨ f , g ⟩ ≈⟨ μ× ⟩∘⟨refl         ⟨
        μ₁ (A × B) ∘ Sub.⟨ f , g ⟩        ∎
    } where open U.HomReasoning
