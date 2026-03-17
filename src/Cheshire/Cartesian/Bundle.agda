{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Cartesian.Bundle where

open import Cheshire.Cartesian.Signature renaming (Cartesian to Signature)
open import Cheshire.Cartesian.Structure

import Cheshire.Category as Category renaming (Category to t; IsCategory to Structure)
import Cheshire.Monoidal.Bundle as Monoidal renaming (Monoidal to t)

record Cartesian o ℓ e : Set (𝕃.suc( o ⊔ ℓ ⊔ e)) where
  field
    𝒬 : Quiver o ℓ
    -- signatures
    category    :  Category.Signature 𝒬
    cartesian   : Signature category
    -- structures
    isCategory  : Category.Structure e category
    isCartesian : IsCartesian isCategory cartesian

  monoidal : Monoidal.t o ℓ e
  monoidal = record
    { 𝒬 = 𝒬
    ; category = category
    ; monoidal = Signature.monoidal cartesian
    ; isCategory = isCategory
    ; isMonoidal = IsCartesian.isMonoidal isCartesian
    }
