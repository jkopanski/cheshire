{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Morphism.Signatures
  {o ℓ} (𝒬 : Quiver o ℓ)
  where

open Quiver 𝒬

infix 4 _⇔_
record _⇔_ (A B : 𝒬 .Ob) : Set (o ⊔ ℓ) where
  field
    from : A ⇒ B
    to   : B ⇒ A
