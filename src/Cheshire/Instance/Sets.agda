{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Sets (o : 𝕃.t) where

import Function
import Data.Product as ×
import Data.Sum as +

import Cheshire.Signatures as Sig
import Cheshire.Object.Signatures as Object

𝒬 : Quiver (𝕃.suc o) o
𝒬 = mk⇒ λ c d → c → d

open Quiver 𝒬
open Object Ob

terminal : Terminal
terminal = record { ⊤ = 𝟙.t }

products : BinaryProducts
products = record { _×_ = ×._×_ }

coproducts : BinaryCoproducts
coproducts = record { _+_ = +._⊎_ }

Sets : Sig.Cartesian 𝒬
Sets = record
  { id = Function.id
  ; _∘_ = Function._∘′_
  ; terminal = terminal
  ; ! = Function.const 𝟙.tt
  ; products = products
  ; π₁ = ×.proj₁
  ; π₂ = ×.proj₂
  ; ⟨_,_⟩ = ×.<_,_>
  }
