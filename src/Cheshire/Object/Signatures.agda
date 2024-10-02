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

record Coproduct (A B : Ob) : Set o where
  field
    A+B : Ob

record BinaryCoProducts : Set o where
  field
    coproduct : ∀ {A B} → Coproduct A B

  private
    module coproduct {A} {B} = Coproduct (coproduct {A} {B})

  infixr 6 _+_
  _+_ : Ob → Ob → Ob
  A + B = coproduct.A+B {A} {B}

record Exponential (A B : Ob) : Set o where
  field
    B^A : Ob
    product : Product B^A A

  module product = Product product

  B^A×A : Ob
  B^A×A = product.A×B
