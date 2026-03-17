{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Bifunctor.Bundle where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Bifunctor.Signature as Signature
open import Cheshire.Bifunctor.Structure

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    e e′ e″ : 𝕃.t

module _
  (C : Category.t o ℓ e) (D : Category.t o′ ℓ′ e′) (E : Category.t o″ ℓ″ e″)
  where

  module C = Category.t C
  module D = Category.t D
  module E = Category.t E

  record Bifunctor : Set (o ⊔ o′ ⊔ o″ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ e ⊔ e′ ⊔ e″) where
    field
      signature : Signature.Bifunctor C.𝒬 D.𝒬 E.𝒬
      structure : IsBifunctor
        C.category D.category E.category
        signature

    open Signature.Bifunctor signature public
    open IsBifunctor structure
