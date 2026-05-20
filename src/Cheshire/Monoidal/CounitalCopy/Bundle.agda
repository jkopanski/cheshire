{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.CounitalCopy.Bundle where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided as Braided renaming (IsBraided to Structure)
import Cheshire.Monoidal.Symmetric as Symmetric renaming (IsSymmetric to Structure)
import Cheshire.Monoidal.CounitalCopy.Signature as Signature renaming (CounitalCopy to t)
import Cheshire.Monoidal.CounitalCopy.Structure as Structure renaming (IsCounitalCopy to t)


record CounitalCopy o ℓ e : Set (𝕃.suc (o ⊔ ℓ ⊔ e)) where
  field
    𝒬           : Quiver o ℓ
    instance eq : Equivalence 𝒬 e
    -- signatures
    category    : Category.Signature 𝒬
    monoidal    : Monoidal.Signature category
    braided     : Braided.Signature monoidal
    counital    : Signature.t monoidal
    -- structures
    isCategory  : Category.Structure eq category
    isMonoidal  : Monoidal.Structure isCategory monoidal
    isBraided   : Braided.Structure isCategory braided
    isCounital  : Structure.t isMonoidal braided counital

  open Category.Signature category public
  open Monoidal.Signature monoidal public
  open Braided.Signature braided public
    hiding (braided-iso)
  open Signature.t counital public
  open Category.Structure isCategory public
  open Monoidal.Structure isMonoidal public
  open Braided.Structure isBraided public
  open Structure.t isCounital public
