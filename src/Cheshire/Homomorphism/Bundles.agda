{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism.Bundles
  {o ℓ e o′ ℓ′ e′} {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′}
  ⦃ eq : Equivalence 𝒮 e ⦄ ⦃ eq′ : Equivalence 𝒯 e′ ⦄
  where

import Data.Product as ×
open × using (Σ-syntax)

import Cheshire.Signatures as Signatures
import Cheshire.Homomorphism.Signatures as Signatures
open import Cheshire.Homomorphism.Structures

record Homomorphism : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    signature : Signatures.Morphism 𝒮 𝒯
    structure : IsMorphism signature

  open Signatures.Morphism signature public
  open IsMorphism structure public

record Functor
  (S : Signatures.Category 𝒮)
  (T : Signatures.Category 𝒯) :
  Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    signature : Signatures.Morphism 𝒮 𝒯
    structure : IsFunctor signature S T

  open Signatures.Morphism signature public
  open IsFunctor structure public

  homomorphism : Homomorphism
  homomorphism = record
    { signature = signature
    ; structure = record { IsFunctor structure }
    }

record Cartesian
  (S : Signatures.Cartesian 𝒮)
  (T : Signatures.Cartesian 𝒯) :
  Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    signature : Signatures.Morphism 𝒮 𝒯
    structure : IsCartesian signature S T

  open Signatures.Morphism signature public
  open IsCartesian structure public

  functor : Functor (S.category) (T.category)
  functor = record
    { signature = signature
    ; structure = record { IsCartesian structure }
    }

  homomorphism : Homomorphism
  homomorphism = record
    { signature = signature
    ; structure = record { IsCartesian structure }
    }
