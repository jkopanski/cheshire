{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Bundle where

import Cheshire.Monoidal.Signature as Signature
open import Cheshire.Monoidal.Structure

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)

record Monoidal o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬           : Quiver o ℓ
    instance eq : Equivalence 𝒬 e
    -- signatures
    category    : Category.Signature 𝒬
    monoidal    : Signature.Monoidal category
    -- structures
    isCategory  : Category.Structure eq category
    isMonoidal  : IsMonoidal isCategory monoidal
