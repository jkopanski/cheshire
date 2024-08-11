{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Homomorphism.Core

module Cheshire.Homomorphism.Signatures
  {o ℓ o′ ℓ′} {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  (ℳ : Morphism 𝒮 𝒯)
  where

open Morphism ℳ

import Cheshire.Object.Signatures as Object

record Terminal (S : Object.Terminal 𝒮) (T : Object.Terminal 𝒯) : Set (o′ ⊔ ℓ′) where
  open Quiver 𝒯
  open Object.Terminal S using () renaming (⊤ to ⊤ₛ)
  open Object.Terminal T renaming (⊤ to ⊤ₜ)
  field
    ε : ⊤ₜ ⇒ F₀ ⊤ₛ

record StrongTerminal (S : Object.Terminal 𝒮) (T : Object.Terminal 𝒯) : Set (o′ ⊔ ℓ′) where
  open Quiver 𝒯
  open Eq 𝒯
  open Object.Terminal S using () renaming (⊤ to ⊤ₛ)
  open Object.Terminal T renaming (⊤ to ⊤ₜ)
  field
    ε : ⊤ₜ ≅ F₀ ⊤ₛ

  module ε = _≅_ ε

record Product {A B}
  (S : Object.Product 𝒮 A B)
  (T : Object.Product 𝒯 (F₀ A) (F₀ B)) :
  Set (o′ ⊔ ℓ′) where
  open Quiver 𝒯
  open Object.Product S using () renaming (A×B to A×Bₛ)
  open Object.Product T renaming (A×B to A×Bₜ)
  field
    μ : A×Bₜ ⇒ F₀ A×Bₛ

record StrongProduct {A B}
  (S : Object.Product 𝒮 A B)
  (T : Object.Product 𝒯 (F₀ A) (F₀ B)) :
  Set (o′ ⊔ ℓ′) where
  open Quiver 𝒯
  open Eq 𝒯
  open Object.Product S using () renaming (A×B to A×Bₛ)
  open Object.Product T renaming (A×B to A×Bₜ)
  field
    μ : A×Bₜ ≅ F₀ A×Bₛ

record BinaryProducts
  (S : Object.BinaryProducts 𝒮)
  (T : Object.BinaryProducts 𝒯) :
  Set (o ⊔ ℓ′) where
  open Quiver 𝒯
  open Object.BinaryProducts S using () renaming (_×_ to _×ₛ_)
  open Object.BinaryProducts T renaming (_×_ to _×ₜ_)
  field
    μ : ∀ {A B} → F₀ A ×ₜ F₀ B ⇒ F₀ (A ×ₛ B)

record StrongBinaryProducts (S : Object.BinaryProducts 𝒮) (T : Object.BinaryProducts 𝒯) : Set (o ⊔ o′ ⊔ ℓ′) where
  open Quiver 𝒯
  open Eq 𝒯
  open Object.BinaryProducts S using () renaming (_×_ to _×ₛ_)
  open Object.BinaryProducts T renaming (_×_ to _×ₜ_)
  field
    μ : ∀ {A B} → F₀ A ×ₜ F₀ B ≅ F₀ (A ×ₛ B)

