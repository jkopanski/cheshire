{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Category.Bundle where

open import Cheshire.Category.Signature renaming (Category to Signature)
open import Cheshire.Category.Structure
import Cheshire.Morphism.Reasoning as MorphismReasoning

record Category o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬           : Quiver o ℓ
    instance eq : Equivalence 𝒬 e
    category    : Signature 𝒬
    isCategory  : IsCategory eq category

  open Signature category public
  open IsCategory isCategory public

  open HomReasoning public
  open Commutation public
  open Equivalence eq public

  module Reasoning = MorphismReasoning isCategory
