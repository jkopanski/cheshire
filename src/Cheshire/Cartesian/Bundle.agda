{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Cartesian.Bundle where

open import Cheshire.Cartesian.Signature renaming (Cartesian to Signature)
open import Cheshire.Cartesian.Structure

import Cheshire.Category.Bundle as Category renaming (Category to t)

private
  variable
    o ℓ : 𝕃.t

record Cartesian (e : 𝕃.t) (𝒬 : Quiver o ℓ) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signature 𝒬
    structure : IsCartesian e signature

  open Signature signature public hiding (category)
  open IsCartesian structure public

  category : Category.t e 𝒬
  category = record
    { signature = Signature.category signature
    ; structure = isCategory
    }

  open Category.t category public
