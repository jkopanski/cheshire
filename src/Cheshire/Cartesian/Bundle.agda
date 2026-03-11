{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Cartesian.Bundle where

open import Cheshire.Cartesian.Signature renaming (Cartesian to Signature)
open import Cheshire.Cartesian.Structure

import Cheshire.Category.Bundle as Category renaming (Category to t)
import Cheshire.Monoidal.Bundle as Monoidal renaming (Monoidal to t)

private
  variable
    o ℓ : 𝕃.t

record Cartesian (e : 𝕃.t) (𝒬 : Quiver o ℓ) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signature 𝒬
    structure : IsCartesian e signature

  open Signature signature public
    hiding (category; monoidal)
  open IsCartesian structure public

  -- This is already exported by monoidal
  -- Perhaps I should do something different here?
  -- category : Category.t e 𝒬
  -- category = record
  --   { signature = Signature.category signature
  --   ; structure = isCategory
  --   }

  -- open Category.t category public
  --   hiding (signature; structure)

  monoidal : Monoidal.t e 𝒬
  monoidal = record
    { signature = Signature.monoidal signature
    ; structure = isMonoidal
    }

  open Monoidal.t monoidal public
    hiding (isCategory)
