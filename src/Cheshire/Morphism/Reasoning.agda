{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Category.Signature
open import Cheshire.Category.Structure

module Cheshire.Morphism.Reasoning
  {o ℓ} {𝒬 : Quiver o ℓ}
  {𝒞 : Category 𝒬}
  {e} (is-𝒞 : IsCategory e 𝒞)
  where

open import Cheshire.Morphism.Reasoning.Core is-𝒞 public
