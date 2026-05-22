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

-- A -- μ₁ A --> B
-- |             |
-- f             f
-- |             |
-- V             V
-- C -- μ₁ B --> D
R₁ : ((A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) → HomPred 𝒬 e
R₁ μ₁ {A} {B} f = U.CommutativeSquare (μ₁ A) f f (μ₁ B)

--   -- R₂ : ((A : I) → Setoids.𝒬 .Hom (H.₀ A × H.₀ A) (H.₀ A)) → HomPred 𝒬 o
--   -- R₂ μ₂ {A} {B} f = CommutativeSquare (μ₂ A) (f U.⁂ f) f (μ₂ B)

--   -- P₀ : ⦃ _ : Terminal (𝒬 .Ob) ⦄ → (μ₀ : (A : I) → Setoids.𝒬 .Hom (H.₀ ⊤) (H.₀ A)) → Prop.Category 𝒞 (R₀ μ₀)
--   -- P₀ μ₀ = record
--   --   { id = λ _ → reflᵢ
--   --   ; _∘_ = λ {g = g} {f} gᴿ fᴿ → λ x → transᵢ (g .cong (fᴿ x)) (gᴿ x)
--   --   }

P₁ : (μ₁ : (A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) → Prop.Category C.category (R₁ μ₁)
P₁ μ₁ = record
  { id = U.identityˡ ○ (⟺ U.identityʳ)
  ; _∘_ = λ {A B C} {g = g} {f} gᴿ fᴿ → begin
      (g ∘ f) ∘ μ₁ A ≈⟨ pullʳ fᴿ ⟩
      g ∘ μ₁ B ∘ f   ≈⟨ pullˡ gᴿ ⟩
      (μ₁ C ∘ g) ∘ f ≈⟨ U.assoc ⟩
      μ₁ C ∘ g ∘ f   ∎
  } where open U.HomReasoning

--   -- P₂ : (μ₂ : (A : I) → Setoids.𝒬 .Hom (H.₀ A × H.₀ A) (H.₀ A)) → Prop.Category 𝒞 (R₂ μ₂)
--   -- P₂ μ₂ = record
--   --   { id = λ _ → reflᵢ
--   --   ; _∘_ = λ {g = g} {f} gᴿ fᴿ → λ x →
--   --       transᵢ (g .cong (fᴿ x)) (gᴿ ((f ⁂ f) .to x))
--   --   }

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

--     -- H.₁ = id
--     -- P₀× :
--     --   (μ₀ : (A : I) → Setoids.𝒬 .Hom (H.₀ ⊤) (H.₀ A)) →
--     --   (∀ {A B} → μ₀ (A × B) ≈ Prop.Cartesian I.cartesian (R₀ μ₀)
--     -- P₀× μ₀ μ₀× = record
--     --   { ! = {!!}
--     --   -- λ where
--     --   --     {A} 𝟙.tt → ⊤-iso.isoʳ
--     --   --       (μ₀ ⊤ .to (to {From = {!!}} (Cartesian.t.id Setoids.t) 𝟙.tt))
--     --   ; π₁ = λ {A B} →
--     --     begin
--     --       H.₁ I.π₁ ∘ μ₀ (A × B)
--     --     -- ≈⟨ insertInner {h = ×-iso.from} {i = ×-iso.to} ×-iso.isoʳ {f = I.π₁} {g = μ₀ (A × B)} ⟩
--     --     --   (I.π₁ ∘ ×-iso.from) ∘ (×-iso.to ∘ μ₀ (A × B))
--     --     ≈⟨ {!!} ⟩
--     --       μ₀ A
--     --     ≈⟨ S.identityˡ {f = μ₀ A} ⟨
--     --       I.id ∘ μ₀ A ∎
--     --   ; π₂ = {!!}
--     --   ; ⟨_,_⟩ = {!!}
--     --   } where open HomReasoning
--     --           μ×≈⟨μ,μ⟩ : ∀ (A B : I) → ×-iso.to ∘ μ₀ (A × B) ≈ S.⟨ μ₀ A , μ₀ B ⟩
--     --           μ×≈⟨μ,μ⟩ A B = begin
--     --             ×-iso.to ∘ μ₀ (A × B) ≈⟨ refl⟩∘⟨ {!!} ⟩
--     --             ×-iso.to ∘ H.₁ {A = ⊤} {B = A × B} I.⟨ μ₀ A , μ₀ B ⟩ ≈⟨ {!!} ⟩
--     --             S.⟨ μ₀ A , μ₀ B ⟩ ∎
--     --           h : ∀ (A B : I) → I.⟨ μ₀ A , μ₀ B ⟩ ≈ μ₀ (A × B)
--     --           h A B = I.unique {!!} {!!}

  P₁× :
    (μ₁ : (A : I) → 𝒰 .Hom (H.₀ A) (H.₀ A)) →
    (∀ {A B : I} → μ₁ (A × B) U.≈ μ₁ A Sub.⁂ μ₁ B) →
    Prop.Cartesian Sub.cartesian (R₁ μ₁)
  P₁× μ₁ μ× = record
    { ! = λ {A} → begin
      (⊤-iso.from ∘ U.!) ∘ μ₁ A ≈⟨ {!!} ⟩ -- λ x → ⊤-iso.isoʳ ((μ₁ ⊤) .to (I.! .to x))
      μ₁ ⊤ ∘ ⊤-iso.from ∘ U.! ∎
    ; π₁ = λ {A B} → {!!} --begin
        -- I.π₁ ∘ μ₁ (A × B)      ≈⟨ U.∘-resp-≈ʳ {f = μ₁ (A × B)} {μ₁ A I.⁂ μ₁ B} {I.π₁} μ× ⟩
        -- I.π₁ ∘ (μ₁ A I.⁂ μ₁ B) ≈⟨ I.π₁∘⁂ {f = μ₁ A} {g = μ₁ B} ⟩
        -- μ₁ A ∘ I.π₁            ∎
    ; π₂ = λ {A B} → {!!} -- begin
        -- I.π₂ ∘ μ₁ (A × B)      ≈⟨ U.∘-resp-≈ʳ {f = μ₁ (A × B)} {μ₁ A I.⁂ μ₁ B} {I.π₂} μ× ⟩
        -- I.π₂ ∘ (μ₁ A I.⁂ μ₁ B) ≈⟨ I.π₂∘⁂ {f = μ₁ A} {g = μ₁ B} ⟩
        -- μ₁ B ∘ I.π₂            ∎
    ; ⟨_,_⟩ = λ {A B C} {f g} fᴿ gᴿ → {!!} -- begin
      --   I.⟨ f , g ⟩ ∘ μ₁ C
      -- ≈⟨ I.∘-distribʳ-⟨⟩ {f = f} {g = g} {q = μ₁ C} ⟩
      --   I.⟨ f ∘ μ₁ C , g ∘ μ₁ C ⟩
      -- ≈⟨ I.⟨⟩-cong₂ {f = f ∘ μ₁ C} {f′ = μ₁ A ∘ f} {g = g ∘ μ₁ C} {g′ = μ₁ B ∘ g} fᴿ gᴿ ⟩
      --   I.⟨ μ₁ A ∘ f , μ₁ B ∘ g ⟩
      -- ≈⟨ I.⁂∘⟨⟩ {f = μ₁ A} {g = μ₁ B} {f′ = f} {g′ = g} ⟨
      --   (μ₁ A I.⁂ μ₁ B) ∘ I.⟨ f , g ⟩
      -- ≈⟨ I.∘-resp-≈ˡ {f = μ₁ (A × B)} {μ₁ A I.⁂ μ₁ B} {I.⟨ f , g ⟩} μ× ⟨
      --   μ₁ (A × B) ∘ I.⟨ f , g ⟩
      -- ∎
    } where open U.HomReasoning
