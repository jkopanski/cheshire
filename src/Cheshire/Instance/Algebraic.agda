{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Algebraic (ℓ : 𝕃.t) where

import Algebra.Bundles as Algebra
import Function.Construct.Identity as Identity

-- import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Homomorphism as Homomorphism renaming (Morphism to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Prop as Prop
import Cheshire.Morphism as Morphisms

import Cheshire.Construction.Sub.Object as Subₒ
import Cheshire.Construction.Sub.Morphism as Subₘ
import Cheshire.Instance.Algebraic.Full ℓ as Full
import Cheshire.Instance.Setoids ℓ as Setoids renaming (Setoids to t)
import Cheshire.Construction.Sub.Algebraic Setoids.t as Sub

open Object
open Homomorphism.t
open Morphisms.Bundles Setoids.category using (_≅_)
open Cartesian.t Setoids.t
open Equivalence Setoids.eq renaming (_≈_ to _≈ₛ_)


------------------------------------------------------------------------
-- Bundle with 1 binary operation
------------------------------------------------------------------------
module Magma where

  module I = Cartesian.t Full.Magma.t
  private module Op₂ = Sub.Op₂ Full.Magma.F₀ Full.Magma.⊤-iso Full.Magma.×-iso

-- ∙ : Setoids.𝒬 .Hom (F₀ (M × M)) (F₀ M)
  ∙ : (A : Algebra.Magma ℓ ℓ) → I.𝒬 .Hom (A × A) A
  ∙ A = Func.binary A.setoid A.∙-cong ∘ ×-iso.to
    where module ×-iso = _≅_ (Full.Magma.×-iso A A)
          module A = Algebra.Magma A

  ∙× : ∀ {A B} → ∙ (A × B) ≈ₛ (∙ A ⁂ ∙ B) ∘ interchange
  ∙× {A} {B} _ = Algebra.Magma.refl A , Algebra.Magma.refl B

  P-∙ = Op₂.P ∙
  P×-∙ = Op₂.P× ∙ λ {A B} → ∙× {A} {B}

  P = P-∙
  P× = P×-∙

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₘ.Bundles.cartesian Full.Magma.t P-∙ P×-∙


------------------------------------------------------------------------
-- Bundle with 1 binary operation & 1 element
------------------------------------------------------------------------
module Monoid where

  module I = Cartesian.t Full.Monoid.t
  private module Op₂ = Sub.Op₂ Algebra.Monoid.setoid Full.Monoid.⊤-iso Full.Monoid.×-iso
  private module Op₀ = Sub.Op₀ Algebra.Monoid.setoid Full.Monoid.⊤-iso Full.Monoid.×-iso

  -- TODO: is this helpful in order to reuse the Magma?
  -- H-∙ : Homomorphism.t I.𝒬 Magma.I.𝒬
  -- H-∙ .F₀ = Algebra.Monoid.magma
  -- H-∙ .F₁ = Function.id

  -- H-∙-isHomo : Homomorphism.IsHomomorphism I.eq Magma.I.eq H-∙
  -- H-∙-isHomo .Homomorphism.IsHomomorphism.F-resp-≈ = Function.id

  -- H-∙-isFunctor : Homomorphism.IsFunctor I.eq Magma.I.eq I.category Magma.I.category H-∙
  -- H-∙-isFunctor = record
  --   { F-resp-id = λ {A} _ → Algebra.Monoid.refl A
  --   ; F-resp-∘ = λ {X Y Z} _ → Algebra.Monoid.refl Z
  --   }

  -- H-∙-isCartesian : Homomorphism.IsCartesian I.eq Magma.I.eq I.cartesian Magma.I.cartesian H-∙
  -- H-∙-isCartesian = record
  --   { ×-iso = λ A B → let
  --       module A = Algebra.Monoid A
  --       module B = Algebra.Monoid B
  --     in record
  --       { from = Identity.function (Full.Magma.F₀ (Algebra.Monoid.magma (A × B)))
  --       ; to = Identity.function (Full.Magma.F₀ (Algebra.Monoid.magma (A × B)))
  --       ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
  --       }
  --   ; F-resp-⟨⟩ = λ {A} {B} _ _ _ → Algebra.Monoid.refl A , Algebra.Monoid.refl B
  --   ; F-resp-π₁ = λ {A} {B} _ → Algebra.Monoid.refl A
  --   ; F-resp-π₂ = λ {A} {B} _ → Algebra.Monoid.refl B
  --   }

  ∙ : (A : Algebra.Monoid ℓ ℓ) → I.𝒬 .Hom (A × A) A
  ∙ A = Magma.∙ (Algebra.Monoid.magma A)

  ∙× : ∀ {A B} → ∙ (A × B) ≈ₛ (∙ A ⁂ ∙ B) ∘ interchange
  ∙× {A} {B} = Magma.∙× {Algebra.Monoid.magma A} {Algebra.Monoid.magma B}

  P-∙ = Op₂.P ∙
  P×-∙ = Op₂.P× ∙ λ {A B} → ∙× {A} {B}

  ε : (A : Algebra.Monoid ℓ ℓ) → I.𝒬 .Hom ⊤ A
  ε A = Func.nullary A.setoid A.ε
    where module A = Algebra.Monoid A

  ε× : ∀ {A B} → ε (A × B) ≈ₛ ⟨ ε A , ε B ⟩
  ε× {A} {B} _ = Algebra.Monoid.refl A , Algebra.Monoid.refl B

  P-ε = Op₀.P ε
  P×-ε = Op₀.P× ε λ {A B} → ε× {A} {B}

  P = P-∙ ∩ P-ε
    where open Prop.Category using (_∩_)
  P× = P×-∙ ∩ P×-ε
    where open Prop.Cartesian using (_∩_)

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₘ.Bundles.cartesian Full.Monoid.t P P×


------------------------------------------------------------------------
-- Bundle with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------
module Group where

  module I = Cartesian.t Full.Group.t
  private module Op₂ = Sub.Op₂ Algebra.Group.setoid Full.Group.⊤-iso Full.Group.×-iso
  private module Op₁ = Sub.Op₁ Algebra.Group.setoid Full.Group.⊤-iso Full.Group.×-iso
  private module Op₀ = Sub.Op₀ Algebra.Group.setoid Full.Group.⊤-iso Full.Group.×-iso

  ∙ : (A : Algebra.Group ℓ ℓ) → I.𝒬 .Hom (A × A) A
  ∙ A = Magma.∙ (Algebra.Group.magma A)

  ∙× : ∀ {A B} → ∙ (A × B) ≈ₛ (∙ A ⁂ ∙ B) ∘ interchange
  ∙× {A} {B} = Magma.∙× {Algebra.Group.magma A} {Algebra.Group.magma B}

  P-∙ = Op₂.P ∙
  P×-∙ = Op₂.P× ∙ λ {A B} → ∙× {A} {B}

  _⁻¹ : (A : Algebra.Group ℓ ℓ) → I.𝒬 .Hom A A
  _⁻¹ A = Func.unary A.setoid A.⁻¹-cong
    where module A = Algebra.Group A

  a⁻¹× : ∀ {A B} → (A × B) ⁻¹ ≈ₛ A ⁻¹ ⁂ B ⁻¹
  a⁻¹× {A} {B} _ = Algebra.Group.refl A , Algebra.Group.refl B

  P-⁻¹ = Op₁.P _⁻¹
  P×-⁻¹ = Op₁.P× _⁻¹ λ {A B} → a⁻¹× {A} {B}

  ε : (A : Algebra.Group ℓ ℓ) → I.𝒬 .Hom ⊤ A
  ε A = Func.nullary A.setoid A.ε
    where module A = Algebra.Group A

  ε× : ∀ {A B} → ε (A × B) ≈ₛ ⟨ ε A , ε B ⟩
  ε× {A} {B} _ = Algebra.Group.refl A , Algebra.Group.refl B

  P-ε = Op₀.P ε
  P×-ε = Op₀.P× ε λ {A B} → ε× {A} {B}

  P = P-∙ ∩ P-ε ∩ P-⁻¹
    where open Prop.Category using (_∩_)
  P× = P×-∙ ∩ P×-ε ∩ P×-⁻¹
    where open Prop.Cartesian using (_∩_)

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₘ.Bundles.cartesian Full.Group.t P P×


------------------------------------------------------------------------
-- Bundle with 2 binary operations & 1 element
------------------------------------------------------------------------
module NearSemiring where

  module I = Cartesian.t Full.NearSemiring.t
  private module Op₂ = Sub.Op₂ Algebra.NearSemiring.setoid Full.NearSemiring.⊤-iso Full.NearSemiring.×-iso
  private module Op₀ = Sub.Op₀ Algebra.NearSemiring.setoid Full.NearSemiring.⊤-iso Full.NearSemiring.×-iso

  + : (A : Algebra.NearSemiring ℓ ℓ) → I.𝒬 .Hom (A × A) A
  + A = Monoid.∙ (Algebra.NearSemiring.+-monoid A)

  +× : ∀ {A B} → + (A × B) ≈ₛ (+ A ⁂ + B) ∘ interchange
  +× {A} {B} = Monoid.∙× {Algebra.NearSemiring.+-monoid A} {Algebra.NearSemiring.+-monoid B}

  P-+ = Op₂.P +
  P×-+ = Op₂.P× + λ {A B} → +× {A} {B}

  0# : (A : Algebra.NearSemiring ℓ ℓ) → I.𝒬 .Hom ⊤ A
  0# A = Monoid.ε (Algebra.NearSemiring.+-monoid A)

  0#× : ∀ {A B} → 0# (A × B) ≈ₛ ⟨ 0# A , 0# B ⟩
  0#× {A} {B} _ = Algebra.NearSemiring.refl A , Algebra.NearSemiring.refl B

  P-0# = Op₀.P 0#
  P×-0# = Op₀.P× 0# λ {A B} → 0#× {A} {B}

  * : (A : Algebra.NearSemiring ℓ ℓ) → I.𝒬 .Hom (A × A) A
  * A = Magma.∙ (Algebra.NearSemiring.*-magma A)

  *× : ∀ {A B} → * (A × B) ≈ₛ (* A ⁂ * B) ∘ interchange
  *× {A} {B} = Magma.∙× {Algebra.NearSemiring.*-magma A} {Algebra.NearSemiring.*-magma B}

  P-* = Op₂.P *
  P×-* = Op₂.P× * λ {A B} → *× {A} {B}

  P = P-+ ∩ P-0# ∩ P-*
    where open Prop.Category using (_∩_)
  P× = P×-+ ∩ P×-0# ∩ P×-*
    where open Prop.Cartesian using (_∩_)

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₘ.Bundles.cartesian Full.NearSemiring.t P P×


------------------------------------------------------------------------
-- Bundles with 2 binary operations & 2 elements
------------------------------------------------------------------------
module Semiring where

  module I = Cartesian.t Full.Semiring.t
  private module Op₂ = Sub.Op₂ Algebra.Semiring.setoid Full.Semiring.⊤-iso Full.Semiring.×-iso
  private module Op₀ = Sub.Op₀ Algebra.Semiring.setoid Full.Semiring.⊤-iso Full.Semiring.×-iso

  + : (A : Algebra.Semiring ℓ ℓ) → I.𝒬 .Hom (A × A) A
  + A = Monoid.∙ (Algebra.Semiring.+-monoid A)

  +× : ∀ {A B} → + (A × B) ≈ₛ (+ A ⁂ + B) ∘ interchange
  +× {A} {B} = Monoid.∙× {Algebra.Semiring.+-monoid A} {Algebra.Semiring.+-monoid B}

  P-+ = Op₂.P +
  P×-+ = Op₂.P× + λ {A B} → +× {A} {B}

  0# : (A : Algebra.Semiring ℓ ℓ) → I.𝒬 .Hom ⊤ A
  0# A = Monoid.ε (Algebra.Semiring.+-monoid A)

  0#× : ∀ {A B} → 0# (A × B) ≈ₛ ⟨ 0# A , 0# B ⟩
  0#× {A} {B} _ = Algebra.Semiring.refl A , Algebra.Semiring.refl B

  P-0# = Op₀.P 0#
  P×-0# = Op₀.P× 0# λ {A B} → 0#× {A} {B}

  * : (A : Algebra.Semiring ℓ ℓ) → I.𝒬 .Hom (A × A) A
  * A = Monoid.∙ (Algebra.Semiring.*-monoid A)

  *× : ∀ {A B} → * (A × B) ≈ₛ (* A ⁂ * B) ∘ interchange
  *× {A} {B} = Monoid.∙× {Algebra.Semiring.*-monoid A} {Algebra.Semiring.*-monoid B}

  P-* = Op₂.P *
  P×-* = Op₂.P× * λ {A B} → *× {A} {B}

  1# : (A : Algebra.Semiring ℓ ℓ) → I.𝒬 .Hom ⊤ A
  1# A = Monoid.ε (Algebra.Semiring.*-monoid A)

  1#× : ∀ {A B} → 1# (A × B) ≈ₛ ⟨ 1# A , 1# B ⟩
  1#× {A} {B} _ = Algebra.Semiring.refl A , Algebra.Semiring.refl B

  P-1# = Op₀.P 1#
  P×-1# = Op₀.P× 1# λ {A B} → 1#× {A} {B}

  P = P-+ ∩ P-0# ∩ P-*
    where open Prop.Category using (_∩_)
  P× = P×-+ ∩ P×-0# ∩ P×-*
    where open Prop.Cartesian using (_∩_)

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₘ.Bundles.cartesian Full.Semiring.t P P×
