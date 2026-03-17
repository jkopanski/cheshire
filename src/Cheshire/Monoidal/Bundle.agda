{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Bundle where

import Cheshire.Monoidal.Signature as Signature
open import Cheshire.Monoidal.Structure

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)

record Monoidal o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬 : Quiver o ℓ
    -- signatures
    category : Category.Signature 𝒬
    monoidal : Signature.Monoidal category
    -- structures
    isCategory : Category.Structure e category
    isMonoidal : IsMonoidal isCategory monoidal


record Braided o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬 : Quiver o ℓ
    -- signatures
    category : Category.Signature 𝒬
    monoidal : Signature.Monoidal category
    braided  : Signature.Braided monoidal
    -- structures
    isCategory : Category.Structure e category
    isMonoidal : IsMonoidal isCategory monoidal
    isBraided  : IsBraided isCategory braided

  open Category.Signature category public
  open Signature.Monoidal monoidal public
  open Signature.Braided braided public
  open Category.Structure isCategory public
  open IsMonoidal isMonoidal public
  open IsBraided isBraided public


record Symmetric o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬 : Quiver o ℓ
    -- signatures
    category : Category.Signature 𝒬
    monoidal : Signature.Monoidal category
    braided  : Signature.Braided monoidal
    -- structures
    isCategory  : Category.Structure e category
    isMonoidal  : IsMonoidal isCategory monoidal
    isBraided   : IsBraided isCategory braided
    isSymmetric : IsSymmetric isCategory braided

  open Category.Signature category public
  open Signature.Monoidal monoidal public
  open Signature.Braided braided public
    hiding (braided-iso)
  open Category.Structure isCategory public
  open IsMonoidal isMonoidal public
  open IsBraided isBraided public
  open IsSymmetric isSymmetric public


record Traced o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬 : Quiver o ℓ
    -- signatures
    category : Category.Signature 𝒬
    monoidal : Signature.Monoidal category
    braided  : Signature.Braided monoidal
    traced   : Signature.Traced monoidal
    -- structures
    isCategory  : Category.Structure e category
    isMonoidal  : IsMonoidal isCategory monoidal
    isBraided   : IsBraided isCategory braided
    isSymmetric : IsSymmetric isCategory braided
    isTraced    : IsTraced isMonoidal braided traced

  open Category.Signature category public
  open Signature.Monoidal monoidal public
  open Signature.Braided braided public
    hiding (braided-iso)
  open Signature.Traced traced public
  open Category.Structure isCategory public
  open IsMonoidal isMonoidal public
  open IsBraided isBraided public
  open IsSymmetric isSymmetric public
  open IsTraced isTraced public
