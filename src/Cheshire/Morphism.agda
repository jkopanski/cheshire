{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Morphism where

import Cheshire.Category as Category
import Cheshire.Morphism.Signatures as Sigs
import Cheshire.Morphism.Structures as Structs
import Cheshire.Morphism.Bundles as MB
import Cheshire.Morphism.Reasoning as MR

module Signatures {o ℓ} (𝒬 : Quiver o ℓ) = Sigs 𝒬
module Structures {o ℓ} {𝒬 : Quiver o ℓ} (𝒞 : Category.Signature 𝒬) = Structs 𝒞
module Bundles {o ℓ} {𝒬 : Quiver o ℓ} (𝒞 : Category.Signature 𝒬) = MB 𝒞
module Reasoning
  {o ℓ e} {𝒬 : Quiver o ℓ}
  {eq : Equivalence 𝒬 e}
  {𝒞 : Category.Signature 𝒬}
  (is-𝒞 : Category.IsCategory eq 𝒞)
  = MR is-𝒞
