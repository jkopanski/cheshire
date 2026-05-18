{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Traced.Bundle where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided as Braided renaming (IsBraided to Structure)
import Cheshire.Monoidal.Symmetric as Symmetric renaming (IsSymmetric to Structure)
import Cheshire.Monoidal.Traced.Signature as Signature renaming (Traced to t)
import Cheshire.Monoidal.Traced.Structure as Structure renaming (IsTraced to t)


record Traced o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬           : Quiver o ℓ
    instance eq : Equivalence 𝒬 e
    -- signatures
    category    : Category.Signature 𝒬
    monoidal    : Monoidal.Signature category
    braided     : Braided.Signature monoidal
    traced      : Signature.t monoidal
    -- structures
    isCategory  : Category.Structure eq category
    isMonoidal  : Monoidal.Structure isCategory monoidal
    isBraided   : Braided.Structure isCategory braided
    isSymmetric : Symmetric.Structure isCategory braided
    isTraced    : Structure.t isMonoidal braided traced

  open Category.Signature category public
  open Monoidal.Signature monoidal public
  open Braided.Signature braided public
    hiding (braided-iso)
  open Signature.t traced public
  open Category.Structure isCategory public
  open Monoidal.Structure isMonoidal public
  open Braided.Structure isBraided public
  open Symmetric.Structure isSymmetric public
  open Structure.t isTraced public
