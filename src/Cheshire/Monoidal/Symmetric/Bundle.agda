{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Symmetric.Bundle where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided as Braided renaming (IsBraided to Structure)
import Cheshire.Monoidal.Symmetric.Structure as Structure renaming (IsSymmetric to t)


record Symmetric o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬           : Quiver o ℓ
    instance eq : Equivalence 𝒬 e
    -- signatures
    category    : Category.Signature 𝒬
    monoidal    : Monoidal.Signature category
    braided     : Braided.Signature monoidal
    -- structures
    isCategory  : Category.Structure eq category
    isMonoidal  : Monoidal.Structure isCategory monoidal
    isBraided   : Braided.Structure isCategory braided
    isSymmetric : Structure.t isCategory braided

  open Category.Signature category public
  open Monoidal.Signature monoidal public
  open Braided.Signature braided public
    hiding (braided-iso)
  open Category.Structure isCategory public
  open Monoidal.Structure isMonoidal public
  open Braided.Structure isBraided public
  open Structure.t isSymmetric public
