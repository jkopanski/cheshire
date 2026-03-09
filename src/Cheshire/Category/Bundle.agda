{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Category.Bundle where

open import Cheshire.Category.Signature renaming (Category to Signature)
open import Cheshire.Category.Structure
import Cheshire.Morphism.Reasoning as MorphismReasoning

private
  variable
    o ℓ : 𝕃.t

record Category (e : 𝕃.t) (𝒬 : Quiver o ℓ) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signature 𝒬
    structure : IsCategory e signature

  open Signature signature public
  open IsCategory structure public

  open HomReasoning public
  open Commutation public
  open Equivalence eq public

  module Reasoning = MorphismReasoning structure
