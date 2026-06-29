{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Algebraic (ℓ : 𝕃.t) where

module Algebra where
  open import Algebra.Bundles public
  module Terminal where
    open import Algebra.Construct.Terminal public
  module Products where
    open import Algebra.Construct.DirectProduct public

import Function.Construct.Constant as Constant
import Function.Construct.Identity as Identity

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Object.Signatures as Object
import Cheshire.Prop as Prop
import Cheshire.Morphism as Morphisms

import Cheshire.Instance.Setoids ℓ as Setoids renaming (Setoids to t)
import Cheshire.Construction.Sub.Homomorphism Setoids.t as Sub
open import Cheshire.Construction.Sub.Morphism using (module Bundles)

open Object
open Quiver Setoids.𝒬 using (_⇒_)
open Morphisms.Bundles Setoids.category using (_≅_)

module Props where
  module _ where
    H₀ : Algebra.Magma ℓ ℓ → Setoid.t ℓ ℓ
    H₀ = Algebra.Magma.setoid

    open Sub H₀

    instance
      terminal : Terminal (Algebra.Magma ℓ ℓ)
      terminal .Terminal.⊤ = Algebra.Terminal.magma

      products : BinaryProducts (Algebra.Magma ℓ ℓ)
      products .BinaryProducts._×_ = Algebra.Products.magma

    ⊤-iso : ⊤ ≅ H₀ ⊤
    ⊤-iso = record
      { from = Constant.function ⊤ (H₀ ⊤) 𝟙.tt
      ; to   = Constant.function ⊤ (H₀ ⊤) 𝟙.tt
      ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
      }

    ×-iso : ∀ A B → H₀ A × H₀ B ≅ H₀ (A × B)
    ×-iso A B = record
      { from = Identity.function (A.setoid × B.setoid)
      ; to = Identity.function (A.setoid × B.setoid)
      ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
      } where module A = Algebra.Magma A
              module B = Algebra.Magma B

    cartesian = Cartesian.t.cartesian (Sub ⊤-iso ×-iso)
    open Cartesian.Signature cartesian
    open Category.Signature (Cartesian.t.category (Sub ⊤-iso ×-iso)) using (_∘_)

    ∙ : (M : Algebra.Magma ℓ ℓ) → H₀ M × H₀ M ⇒ H₀ M
    ∙ M = Func.binary M.setoid M.∙-cong
      where module M = Algebra.Magma M

    -- Don't you just love it whene you have to fill in all the
    -- implicit when working in concrete categories?
    ∙-× :
      ∀ {A B : Algebra.Magma ℓ ℓ} →
      ∙ (A × B) ≈ _∘_ {A = (A × B) × (A × B)} {(A × A) × (B × B)} {A × B}
        (_⁂_ {A = A × A} {A} {B × B} {B} (∙ A) (∙ B))
        (interchange {A} {B} {A} {B})
    ∙-× {A} {B} ((a₁ , b₁) , (a₂ , b₂)) = A.refl , B.refl
      where module A = Algebra.Magma A
            module B = Algebra.Magma B

    P-∙ : Prop.Cartesian
      cartesian
      (λ {A B} → R₂ ⊤-iso ×-iso ∙ {A} {B})
    P-∙ = P₂× ⊤-iso ×-iso ∙ (λ {A B} → ∙-× {A} {B})

    Magma : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
    Magma = Bundles.cartesian (Sub ⊤-iso ×-iso) (λ {A B} → R₂ ⊤-iso ×-iso ∙ {A} {B}) (Prop.Cartesian.category P-∙) P-∙
