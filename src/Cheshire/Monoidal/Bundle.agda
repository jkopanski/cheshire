{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Bundle where

import Cheshire.Monoidal.Signature as Signature
open import Cheshire.Monoidal.Structure

import Cheshire.Category.Bundle as Category renaming (Category to t)

private
  variable
    o ℓ : 𝕃.t

record Monoidal (e : 𝕃.t) (𝒬 : Quiver o ℓ) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signature.Monoidal 𝒬
    structure : IsMonoidal e signature

  open Signature.Monoidal signature public hiding (category)
  open IsMonoidal structure public

  category : Category.t e 𝒬
  category = record
    { signature = Signature.Monoidal.category signature
    ; structure = isCategory
    }

  open Category.t category public

record Braided (e : 𝕃.t) (𝒬 : Quiver o ℓ) : Set (𝕃.suc o ⊔ 𝕃.suc ℓ ⊔ 𝕃.suc e) where
  field
    signature : Signature.Braided 𝒬
    structure : IsBraided e signature

  open Signature.Braided signature public hiding (category; monoidal)
  open IsBraided structure public

  monoidal : Monoidal e 𝒬
  monoidal = record
    { signature = Signature.Braided.monoidal signature
    ; structure = isMonoidal
    }

