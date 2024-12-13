{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Bundles
  {o ℓ} (𝒬 : Quiver o ℓ)
  where

import Data.Product as ×
open × using (Σ-syntax)

import Cheshire.Morphism.Reasoning as MorReasoning
import Cheshire.Signatures 𝒬 as Signatures
open import Cheshire.Structures

record Category (e : 𝕃.t) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signatures.Category
    structure : IsCategory e signature

  open Signatures.Category signature public
  open IsCategory structure public

  open HomReasoning public
  open Commutation public

  module Reasoning = MorReasoning structure
