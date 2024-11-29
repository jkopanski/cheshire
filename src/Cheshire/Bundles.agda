{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Bundles
  {o ℓ e} (𝒬 : Quiver o ℓ)
  ⦃ eq : Equivalence 𝒬 e ⦄
  where

import Data.Product as ×
open × using (Σ-syntax)

import Cheshire.Signatures 𝒬 as Signatures
open import Cheshire.Structures

record Category : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ e) where
  field
    signature : Signatures.Category
    structure : IsCategory signature

  open Signatures.Category signature public
  open IsCategory structure public
