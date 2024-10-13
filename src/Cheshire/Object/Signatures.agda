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

open Terminal ⦃ … ⦄ public

record Product (A B : Ob) : Set o where
  field
    A×B : Ob

open Product ⦃ … ⦄ public

record BinaryProducts : Set o where
  infixr 7 _×_
  field
    _×_ : Ob → Ob → Ob

  product : ∀ {A B} → Product A B
  product {A} {B} = record { A×B = A × B }

open BinaryProducts ⦃ … ⦄ public

instance
  productBinaryProducts : ∀ {A B} → ⦃ BinaryProducts ⦄ → Product A B
  productBinaryProducts {A} {B} = product

record Coproduct (A B : Ob) : Set o where
  field
    A+B : Ob

open Coproduct ⦃ … ⦄ public

record BinaryCoproducts : Set o where
  infixr 6 _+_
  field
    _+_ : Ob → Ob → Ob

  coproduct : ∀ {A B} → Coproduct A B
  coproduct {A} {B} = record { A+B = A + B }

open BinaryCoproducts ⦃ … ⦄ public

instance
  coproductBinaryCoproducts : ∀ {A B} → ⦃ BinaryCoproducts ⦄ → Coproduct A B
  coproductBinaryCoproducts {A} {B} = coproduct

-- Wait for actual usage
-- record Exponential (A B : Ob) : Set o where
--   field
--     B^A : Ob
--     B^A×A : Product B^A A

--   module product = Product B^A×A

-- open Exponential ⦃ … ⦄ public
