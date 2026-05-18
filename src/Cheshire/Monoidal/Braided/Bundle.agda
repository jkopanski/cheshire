{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Braided.Bundle where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided.Signature as Signature renaming (Braided to t)
import Cheshire.Monoidal.Braided.Structure as Structure renaming (IsBraided to t)


record Braided o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬           : Quiver o ℓ
    instance eq : Equivalence 𝒬 e
    -- signatures
    category    : Category.Signature 𝒬
    monoidal    : Monoidal.Signature category
    braided     : Signature.t monoidal
    -- structures
    isCategory  : Category.Structure eq category
    isMonoidal  : Monoidal.Structure isCategory monoidal
    isBraided   : Structure.t isCategory braided

  open Category.Signature category public
  open Monoidal.Signature monoidal public
  open Signature.t braided public
  open Category.Structure isCategory public
  open Monoidal.Structure isMonoidal public
  open Structure.t isBraided public

