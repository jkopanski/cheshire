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
  {𝒞 : Quiver o ℓ} {𝒟 : Quiver o′ ℓ′} {ℰ : Quiver o″ ℓ″}
  (C : Category.t e 𝒞) (D : Category.t e′ 𝒟) (E : Category.t e″ ℰ)
  where

  module C = Category.t C
  module D = Category.t D
  module E = Category.t E

  record Bifunctor : Set (o ⊔ o′ ⊔ o″ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ e ⊔ e′ ⊔ e″) where
    field
      signature : Signature.Bifunctor 𝒞 𝒟 ℰ
      structure : IsBifunctor
        {C = C.signature} {D = D.signature} {E = E.signature}
        C.eq D.eq E.eq
        signature

    open Signature.Bifunctor signature public
    open IsBifunctor structure
