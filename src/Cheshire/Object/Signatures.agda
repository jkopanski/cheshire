{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Object.Signatures
  {o} (Ob : Set o)
  where

private
  variable
    A B C : Ob

record Terminal : Set o where
  field
    ⊤ : Ob

record Product (A B : Ob) : Set o where
  field
    A×B : Ob

record BinaryProducts : Set o where
  field
    product : ∀ {A B} → Product A B

  private
    module product {A} {B} = Product (product {A} {B})

  infixr 7 _×_
  _×_ : Ob → Ob → Ob
  A × B = Product.A×B (product {A} {B})
