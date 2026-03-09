{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Bundle where

open import Cheshire.Monoidal.Signature renaming (Monoidal to Signature)
open import Cheshire.Monoidal.Structure

import Cheshire.Category.Bundle as Category renaming (Category to t)

private
  variable
    o ℓ : 𝕃.t

record Monoidal (e : 𝕃.t) (𝒬 : Quiver o ℓ) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signature 𝒬
    structure : IsMonoidal e signature

  open Signature signature public hiding (category)
  open IsMonoidal structure public

  category : Category.t e 𝒬
  category = record
    { signature = Signature.category signature
    ; structure = isCategory
    }

  open Category.t category public
