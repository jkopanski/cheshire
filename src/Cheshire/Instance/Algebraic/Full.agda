{-# OPTIONS --safe #-}

-- This module defines what is commonly called _Full sub category_.
-- That is sub category formed by object morphism
-- (`Cheshire.Construct.Sub.Object`).  In order to define Cartesian
-- category for each of the Algebra (is that the right use of the
-- word?  I mean records defined in the `Algebra.Bundles`, like Magma,
-- Semigroup etc.) I need `Terminal` and `BinaryProducts` instance for
-- each Algebra signature.  I thought that I could perhaps use `Raw*`
-- variants but those don't provide projections to `Setoid`, only
-- `RawSetoid`.

open import Cheshire.Core
open import Overture using (module ×)

module Cheshire.Instance.Algebraic.Full (ℓ : 𝕃.t) where

module Algebra where
  open import Algebra.Bundles public
  open import Algebra.Lattice.Bundles public

  private
    variable
      a b c ℓ₁ ℓ₂ : 𝕃.t

  module Terminal where
    open import Algebra.Construct.Terminal public
    open import Algebra.Lattice.Construct.Zero public

    -- is this good?
    -- I have no idea what I am doing, just monkey see, monkey do
    ringWithoutOne : ∀ {c ℓ} → RingWithoutOne c ℓ
    ringWithoutOne {c} {ℓ} = record { 𝕆ne {c} {ℓ} }

    quasigroup : ∀ {c ℓ} → Quasigroup c ℓ
    quasigroup {c} {ℓ} = record { 𝕆ne {c} {ℓ} }

    loop : ∀ {c ℓ} → Loop c ℓ
    loop {c} {ℓ} = record { 𝕆ne {c} {ℓ} }

    kleeneAlgebra : ∀ {c ℓ} → KleeneAlgebra c ℓ
    kleeneAlgebra {c} {ℓ} = record { 𝕆ne {c} {ℓ} }

  module Products where
    open import Algebra.Construct.DirectProduct public
    open import Algebra.Lattice.Construct.DirectProduct public
    open import Data.Product.Relation.Binary.Pointwise.NonDependent
    open ×

    rawNearSemiring : RawNearSemiring a ℓ₁ → RawNearSemiring b ℓ₂ → RawNearSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
    rawNearSemiring R S = record
      { Carrier = R.Carrier × S.Carrier
      ; _≈_     = Pointwise R._≈_ S._≈_
      ; _+_     = zip R._+_ S._+_
      ; _*_     = zip R._*_ S._*_
      ; 0#      = R.0# , S.0#
      } where module R = RawNearSemiring R; module S = RawNearSemiring S

    nearSemiring : NearSemiring a ℓ₁ → NearSemiring b ℓ₂ → NearSemiring (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
    nearSemiring R S = record
      { isNearSemiring = record
          { +-isMonoid = Monoid.isMonoid (monoid R.+-monoid S.+-monoid)
          ; *-cong     = zip R.*-cong S.*-cong
          ; *-assoc    = λ x y z → (R.*-assoc , S.*-assoc) <*> x <*> y <*> z
          ; distribʳ   = λ x y z → (R.distribʳ , S.distribʳ) <*> x <*> y <*> z
          ; zeroˡ      = uncurry (λ x y → R.zeroˡ x , S.zeroˡ y)
          }
      } where module R = NearSemiring R; module S = NearSemiring S

import Function.Construct.Constant as Constant
import Function.Construct.Identity as Identity

import Cheshire.Cartesian as Cartesian renaming (Cartesian to t; IsCartesian to Structure)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms
import Cheshire.Instance.Setoids ℓ as Setoids renaming (Setoids to t)
import Cheshire.Construction.Sub.Object as Subₒ

open Object
open Morphisms.Bundles Setoids.category using (_≅_)

------------------------------------------------------------------------
-- Bundle with 1 binary operation
------------------------------------------------------------------------
module Magma where

  F₀ : Algebra.Magma ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Magma.setoid

  instance
    terminal : Terminal (Algebra.Magma ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.magma

    products : BinaryProducts (Algebra.Magma ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.magma

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Magma A
            module B = Algebra.Magma B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


------------------------------------------------------------------------
-- Bundle with 1 binary operation & 1 element
------------------------------------------------------------------------
module Monoid where

  F₀ : Algebra.Monoid ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Monoid.setoid

  instance
    terminal : Terminal (Algebra.Monoid ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.monoid

    products : BinaryProducts (Algebra.Monoid ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.monoid

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Monoid A
            module B = Algebra.Monoid B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


------------------------------------------------------------------------
-- Bundle with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------
module Group where

  F₀ : Algebra.Group ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Group.setoid

  instance
    terminal : Terminal (Algebra.Group ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.group

    products : BinaryProducts (Algebra.Group ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.group

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Group A
            module B = Algebra.Group B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


------------------------------------------------------------------------
-- Bundle with 2 binary operations & 1 element
------------------------------------------------------------------------
module NearSemiring where

  F₀ : Algebra.NearSemiring ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.NearSemiring.setoid

  instance
    terminal : Terminal (Algebra.NearSemiring ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.nearSemiring

    products : BinaryProducts (Algebra.NearSemiring ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.nearSemiring

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.NearSemiring A
            module B = Algebra.NearSemiring B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso

------------------------------------------------------------------------
-- Bundles with 2 binary operations & 2 elements
------------------------------------------------------------------------
module Semiring where

  F₀ : Algebra.Semiring ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Semiring.setoid

  instance
    terminal : Terminal (Algebra.Semiring ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.semiring

    products : BinaryProducts (Algebra.Semiring ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.semiring

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Semiring A
            module B = Algebra.Semiring B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------
module RingWithoutOne where

  F₀ : Algebra.RingWithoutOne ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.RingWithoutOne.setoid

  instance
    terminal : Terminal (Algebra.RingWithoutOne ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.ringWithoutOne

    products : BinaryProducts (Algebra.RingWithoutOne ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.ringWithoutOne

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.RingWithoutOne A
            module B = Algebra.RingWithoutOne B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------
module Ring where

  F₀ : Algebra.Ring ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Ring.setoid

  instance
    terminal : Terminal (Algebra.Ring ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.ring

    products : BinaryProducts (Algebra.Ring ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.ring

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Ring A
            module B = Algebra.Ring B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


------------------------------------------------------------------------
-- Bundles with 3 binary operations
------------------------------------------------------------------------
module Quasigroup where

  F₀ : Algebra.Quasigroup ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Quasigroup.setoid

  instance
    terminal : Terminal (Algebra.Quasigroup ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.quasigroup

    products : BinaryProducts (Algebra.Quasigroup ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.quasigroup

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Quasigroup A
            module B = Algebra.Quasigroup B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso

------------------------------------------------------------------------
-- Bundles with 3 binary operations & 1 element
------------------------------------------------------------------------
module Loop where

  F₀ : Algebra.Loop ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.Loop.setoid

  instance
    terminal : Terminal (Algebra.Loop ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.loop

    products : BinaryProducts (Algebra.Loop ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.loop

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.Loop A
            module B = Algebra.Loop B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso


module KleeneAlgebra where

  F₀ : Algebra.KleeneAlgebra ℓ ℓ → Setoid.t ℓ ℓ
  F₀ = Algebra.KleeneAlgebra.setoid

  instance
    terminal : Terminal (Algebra.KleeneAlgebra ℓ ℓ)
    terminal .Terminal.⊤ = Algebra.Terminal.kleeneAlgebra

    products : BinaryProducts (Algebra.KleeneAlgebra ℓ ℓ)
    products .BinaryProducts._×_ = Algebra.Products.kleeneAlgebra

  ⊤-iso : ⊤ ≅ F₀ ⊤
  ⊤-iso = record
    { from = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; to   = Constant.function ⊤ (F₀ ⊤) 𝟙.tt
    ; isIso = record { isoˡ = λ _ → 𝟙.tt; isoʳ = λ _ → 𝟙.tt }
    }

  ×-iso : ∀ A B → F₀ A × F₀ B ≅ F₀ (A × B)
  ×-iso A B = record
    { from = Identity.function (A.setoid × B.setoid)
    ; to = Identity.function (A.setoid × B.setoid)
    ; isIso = record { isoˡ = λ _ → A.refl , B.refl; isoʳ = λ _ → A.refl , B.refl }
    } where module A = Algebra.KleeneAlgebra A
            module B = Algebra.KleeneAlgebra B

  t : Cartesian.t (𝕃.suc ℓ) ℓ ℓ
  t = Subₒ.Bundles.cartesian Setoids.t F₀ ⊤-iso ×-iso
