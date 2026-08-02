{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Algebraic.Module (ℓ : 𝕃.t) where

module Algebra where
  open import Algebra.Bundles public
  open import Algebra.Module.Bundles public

  module Terminal where
    open import Algebra.Module.Construct.Zero public

  module Products where
    open import Algebra.Module.Construct.DirectProduct public

import Function.Construct.Constant as Constant
import Function.Construct.Identity as Identity

import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Object.Signatures as Object
import Cheshire.Prop as Prop
import Cheshire.Morphism as Morphisms
import Cheshire.Instance.Setoids ℓ as Setoids renaming (Setoids to t)
import Cheshire.Instance.Algebraic ℓ as Algebraic
import Cheshire.Construction.Sub.Object as Subₒ
import Cheshire.Construction.Sub.Morphism as Subₘ
import Cheshire.Construction.Sub.Algebraic Setoids.t as Sub

open Object
open Morphisms.Bundles Setoids.category using (_≅_)
open Cartesian.t Setoids.t hiding (terminal; products)
open Equivalence Setoids.eq renaming (_≈_ to _≈ₛ_)

module LeftSemimodule {r ℓr} (R : Algebra.Semiring r ℓr) where

  F₀ : Algebra.LeftSemimodule R ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.LeftSemimodule.≈ᴹ-setoid

  instance
    terminal : Terminal (Algebra.LeftSemimodule R ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.leftSemimodule

    products : BinaryProducts (Algebra.LeftSemimodule R ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.leftSemimodule

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.≈ᴹ-setoid × B.≈ᴹ-setoid)
    ; to = Identity.function (A.≈ᴹ-setoid × B.≈ᴹ-setoid)
    ; isIso = record { isoˡ = λ _ → A.≈ᴹ-refl , B.≈ᴹ-refl; isoʳ = λ _ → A.≈ᴹ-refl , B.≈ᴹ-refl }
    } where module A = Algebra.LeftSemimodule A
            module B = Algebra.LeftSemimodule B

  I : Cartesian.t (𝕃.suc ℓ ⊔ r ⊔ ℓr) ℓ ℓ
  I = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso

  module I = Cartesian.t I
  module R = Algebra.Semiring R
  private module Op₂ = Sub.Op₂ Algebra.LeftSemimodule.≈ᴹ-setoid ⊤-iso ×-iso
  private module Op₁ = Sub.Op₁ Algebra.LeftSemimodule.≈ᴹ-setoid ⊤-iso ×-iso
  private module Op₀ = Sub.Op₀ Algebra.LeftSemimodule.≈ᴹ-setoid ⊤-iso ×-iso
  private module Act = Sub.Action Algebra.LeftSemimodule.≈ᴹ-setoid ⊤-iso ×-iso R.Carrier

  +ᴹ : (A : Algebra.LeftSemimodule R ℓ ℓ) → I.𝒬 .Hom (A × A) A
  +ᴹ A = Func.binary A.≈ᴹ-setoid A.+ᴹ-cong ∘ ×-iso.to
    where module A = Algebra.LeftSemimodule A
          module ×-iso = _≅_ (×-iso A A)

  +ᴹ× : ∀ {A B} → +ᴹ (A × B) ≈ₛ (+ᴹ A ⁂ +ᴹ B) ∘ interchange
  +ᴹ× {A} {B} _ = Algebra.LeftSemimodule.≈ᴹ-refl A , Algebra.LeftSemimodule.≈ᴹ-refl B

  P-+ᴹ = Op₂.P +ᴹ
  P×-+ᴹ = Op₂.P× +ᴹ λ {A B} → +ᴹ× {A} {B}

  0ᴹ : (A : Algebra.LeftSemimodule R ℓ ℓ) → I.𝒬 .Hom ⊤ A
  0ᴹ A = Algebraic.Monoid.ε (Algebra.LeftSemimodule.+ᴹ-monoid A)

  0ᴹ× : ∀ {A B} → 0ᴹ (A × B) ≈ₛ ⟨ 0ᴹ A , 0ᴹ B ⟩
  0ᴹ× {A} {B} _ = Algebra.LeftSemimodule.≈ᴹ-refl A , Algebra.LeftSemimodule.≈ᴹ-refl B

  P-0ᴹ = Op₀.P 0ᴹ
  P×-0ᴹ = Op₀.P× 0ᴹ λ {A B} → 0ᴹ× {A} {B}

  *ˡ : (A : Algebra.LeftSemimodule R ℓ ℓ) → R.Carrier → I.𝒬 .Hom A A
  *ˡ A = λ (r : R.Carrier) → Func.unary A.≈ᴹ-setoid (A.*ₗ-cong {r} R.refl)
    where module A = Algebra.LeftSemimodule A

  *ˡ× : ∀ {A B} → (r : R.Carrier) → *ˡ (A × B) r ≈ₛ *ˡ A r ⁂ *ˡ B r
  *ˡ× {A} {B} r _ = A.≈ᴹ-refl , B.≈ᴹ-refl
    where module A = Algebra.LeftSemimodule A
          module B = Algebra.LeftSemimodule B

  P-*ˡ = Act.P *ˡ
  P×-*ˡ = Act.P× *ˡ λ {A B} → *ˡ× {A} {B}

  P = P-+ᴹ ∩ P-0ᴹ ∩ P-*ˡ
    where open Prop.Category using (_∩_)
  P× = P×-+ᴹ ∩ P×-0ᴹ ∩ P×-*ˡ
    where open Prop.Cartesian using (_∩_)

  t : Cartesian.t (𝕃.suc ℓ ⊔ r ⊔ ℓr) (ℓ ⊔ r) ℓ
  t = Subₘ.Bundles.cartesian I P P×
