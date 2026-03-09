{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Constant.Signatures where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Homomorphism.Signatures as Morphism renaming (Morphism to t)

import Cheshire.Instance.One as One renaming (One0 to t)
import Cheshire.Construction.Product.Signatures as Product

open Morphism using (id)
open Product using (_※_)

private
  variable
    o ℓ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ

constant : Category.t 𝒯 → 𝒯 .Ob → Morphism.t 𝒮 𝒯
constant T t = record
  { F₀ = const t
  ; F₁ = const T.id
  } where module T = Category.t T

constant! : Category.t 𝒯 → 𝒯 .Ob → Morphism.t One.𝒬0 𝒯
constant! = constant

constantˡ : Category.t 𝒮 → 𝒮 .Ob → Morphism.t 𝒯 (Product.𝒬 𝒮 𝒯)
constantˡ S s = constant S s ※ id

constantʳ : Category.t 𝒮 → 𝒮 .Ob → Morphism.t 𝒯 (Product.𝒬 𝒯 𝒮)
constantʳ S s = id ※ constant S s
