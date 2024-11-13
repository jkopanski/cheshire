{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Signatures using (Category)

module Cheshire.Morphism.Bundles
  {o ℓ} {𝒬 : Quiver o ℓ} (𝒞 : Category 𝒬)
  where

import Data.Product as ×
open × using (Σ; Σ-syntax)

import Cheshire.Morphism.Signatures 𝒬 as Signatures
import Cheshire.Morphism.Structures 𝒞 as Structures

open Quiver 𝒬 using (_⇒_)
open Category 𝒞
open Signatures using (_⇔_)
open Structures using (IsEpi; IsIso; IsMono)

private
  variable
    e : 𝕃.t
    A B C : 𝒬 .Ob

record _↣_ ⦃ eq : Equivalence 𝒬 e ⦄ (A B : 𝒬 .Ob) : Set (o ⊔ ℓ ⊔ e) where
  field
    mor : A ⇒ B
    isMono : IsMono mor

-- A ↣ B
Mono : ⦃ Equivalence 𝒬 e ⦄ → (A B : 𝒬 .Ob) → Set (o ⊔ ℓ ⊔ e)
Mono A B = Σ (A ⇒ B) IsMono

record _↠_ ⦃ eq : Equivalence 𝒬 e ⦄ (A B : 𝒬 .Ob) : Set (o ⊔ ℓ ⊔ e) where
  field
    mor : A ⇒ B
    isEpi : IsEpi mor

-- A ↠ B
Epi : ⦃ Equivalence 𝒬 e ⦄ → (A B : 𝒬 .Ob) → Set (o ⊔ ℓ ⊔ e)
Epi A B = Σ (A ⇒ B) IsEpi

infix 4 _≅_
record _≅_ ⦃ eq : Equivalence 𝒬 e ⦄ (A B : 𝒬 .Ob) : Set (o ⊔ ℓ ⊔ e) where
  field
    from  : A ⇒ B
    to    : B ⇒ A
    isIso : IsIso from to

  open IsIso isIso public

Iso : ⦃ Equivalence 𝒬 e ⦄ → (A B : 𝒬 .Ob) → Set (o ⊔ ℓ ⊔ e)
Iso A B = Σ[ iso ∈ A ⇔ B ] IsIso (iso .from) (iso .to)
  where open _⇔_
