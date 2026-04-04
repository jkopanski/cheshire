{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Category.Signature
open import Cheshire.Category.Structure

module Cheshire.Morphism.Reasoning
  {o ℓ e} {𝒬 : Quiver o ℓ}
  {eq : Equivalence 𝒬 e}
  {𝒞 : Category 𝒬}
  (is-𝒞 : IsCategory eq 𝒞)
  where

open import Cheshire.Morphism.Reasoning.Core is-𝒞 public
