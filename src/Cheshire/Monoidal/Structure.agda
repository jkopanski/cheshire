{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Structure where

import Cheshire.Morphism as Morphisms
import Cheshire.Natural as Natural
open import Cheshire.Category.Structure
open import Cheshire.Monoidal.Signature

private
  variable
    o ℓ : 𝕃.t

record IsMonoidal (e : 𝕃.t) {𝒬 : Quiver o ℓ} (ℳ : Monoidal 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Monoidal ℳ
  field
    isCategory : IsCategory e category

  open IsCategory isCategory public
  open HomReasoning
  open Commutation
  open Morphisms.Bundles category
  open Morphisms.Reasoning isCategory

  field
    unitorˡ    : ∀ {X} → unit ⊗₀ X ≅ X
    unitorʳ    : ∀ {X} → X ⊗₀ unit ≅ X
    associator : ∀ {X Y Z} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

  module unitorˡ {X} = _≅_ (unitorˡ {X = X})
  module unitorʳ {X} = _≅_ (unitorʳ {X = X})
  module associator {X} {Y} {Z} = _≅_ (associator {X} {Y} {Z})

  private
    λ⇒ = unitorˡ.from
    λ⇐ = unitorˡ.to
    ρ⇒ = unitorʳ.from
    ρ⇐ = unitorʳ.to
    α⇒ = associator.from
    α⇐ = associator.to

  field
    unitorˡ-commute-from :
      ∀ {X Y} {f : X ⇒ Y} →
      CommutativeSquare (id ⊗₁ f) λ⇒ λ⇒ f
    unitorˡ-commute-to :
      ∀ {X Y} {f : X ⇒ Y} →
      CommutativeSquare f λ⇐ λ⇐ (id ⊗₁ f)
    unitorʳ-commute-from :
      ∀ {X Y} {f : X ⇒ Y} →
      CommutativeSquare (f ⊗₁ id) ρ⇒ ρ⇒ f
    unitorʳ-commute-to :
      ∀ {X Y} {f : X ⇒ Y} →
      CommutativeSquare f ρ⇐ ρ⇐ (f ⊗₁ id)
    assoc-commute-from :
      ∀ {X Y W Z A B} {f : X ⇒ Y} {g : W ⇒ Z} {h : A ⇒ B} →
      CommutativeSquare ((f ⊗₁ g) ⊗₁ h) α⇒ α⇒ (f ⊗₁ (g ⊗₁ h))
    assoc-commute-to :
      ∀ {X Y W Z A B} {f : X ⇒ Y} {g : W ⇒ Z} {h : A ⇒ B} →
      CommutativeSquare (f ⊗₁ (g ⊗₁ h)) α⇐ α⇐ ((f ⊗₁ g) ⊗₁ h)
    triangle :
      ∀ {X Y} →
      [ (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
        α⇒          ⇒⟨ X ⊗₀ (unit ⊗₀ Y) ⟩
        id ⊗₁ λ⇒
        ≈ ρ⇒ ⊗₁ id
      ⟩
    pentagon :
      ∀ {X Y Z W} →
      [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨
        α⇒ ⊗₁ id        ⇒⟨ (X ⊗₀ Y ⊗₀ Z) ⊗₀ W ⟩
        α⇒              ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⊗₀ W ⟩
        id ⊗₁ α⇒
      ≈ α⇒              ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⊗₀ W ⟩
        α⇒
      ⟩


record IsBraided (e : 𝕃.t) {𝒬 : Quiver o ℓ} (ℳ : Braided 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Braided ℳ
  field
    isMonoidal : IsMonoidal e monoidal

  open IsMonoidal isMonoidal public
  open HomReasoning
  open Commutation
  open Morphisms.Reasoning isCategory

  field
    braiding-isIso : Natural.IsIsomorphism isCategory braiding

  field
    hexagon₁ :
      ∀ {X Y Z} →
      [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
        B  ⊗₁ id                    ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
        associator.from             ⇒⟨ Y ⊗₀ X ⊗₀ Z ⟩
        id ⊗₁ B
      ≈ associator.from             ⇒⟨ X ⊗₀ Y ⊗₀ Z ⟩
        B                           ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
        associator.from
      ⟩
    hexagon₂ :
      ∀ {X Y Z} →
      [ X ⊗₀ Y ⊗₀ Z ⇒ (Z ⊗₀ X) ⊗₀ Y ]⟨
        id ⊗₁ B                     ⇒⟨ X ⊗₀ Z ⊗₀ Y ⟩
        (associator.to              ⇒⟨ (X ⊗₀ Z) ⊗₀ Y ⟩
        B ⊗₁ id)
      ≈ associator.to               ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⟩
        (B                          ⇒⟨ Z ⊗₀ X ⊗₀ Y ⟩
        associator.to)
      ⟩


record IsSymmetric (e : 𝕃.t) {𝒬 : Quiver o ℓ} (ℳ : Braided 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Braided ℳ
  field
    isBraided : IsBraided e ℳ

  open IsBraided isBraided public
  open Morphisms.Signatures 𝒬
  open Morphisms.Structures category
  open Morphisms.Bundles category

  field
    commutative : ∀ {X Y} → B {X} {Y} ∘ B {Y} {X} ≈ id

  braided-isIso : ∀ {X Y} → IsIso (B {X} {Y}) B
  braided-isIso = record
    { isoˡ = commutative
    ; isoʳ = commutative
    }

  braided : ∀ {X Y} → X ⊗₀ Y ≅ Y ⊗₀ X
  braided = record
    { _⇔_ braided-iso
    ; isIso = braided-isIso
    }

record IsTraced (e : 𝕃.t) {𝒬 : Quiver o ℓ} (ℳ : Traced 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Traced ℳ
  field
    isSymmetric : IsSymmetric e symmetric

  open IsSymmetric isSymmetric public

  field
    trace-resp-≈ :
      ∀ {X A B} {f g : A ⊗₀ X ⇒ B ⊗₀ X} →
      f ≈ g → trace f ≈ trace g

    slide :
      ∀ {X Y A B} {f : A ⊗₀ X ⇒ B ⊗₀ Y} {g : Y ⇒ X} →
      trace (f ∘ id ⊗₁ g) ≈ trace (id ⊗₁ g ∘ f)
    tightenₗ :
      ∀ {X A B C} {f : B ⇒ C} {g : A ⊗₀ X ⇒ B ⊗₀ X} →
      trace (f ⊗₁ id ∘ g) ≈ f ∘ trace g
    tightenᵣ :
      ∀ {X A B C} {f : B ⊗₀ X ⇒ C ⊗₀ X} {g : A ⇒ B} →
      trace (f ∘ g ⊗₁ id) ≈ trace f ∘ g

    vanishing₁ :
      ∀ {X Y} {f : X ⇒ Y} →
      trace {X = unit} (f ⊗₁ id) ≈ f
    vanishing₂ :
      ∀ {A B X Y} {f : A ⊗₀ X ⊗₀ Y ⇒ B ⊗₀ X ⊗₀ Y} →
      trace {X = X} (trace {X = Y} (associator.to ∘ f ∘ associator.from))
      ≈ trace {X = X ⊗₀ Y} f
    superposing :
      ∀ {A B X Y} {f : A ⊗₀ X ⇒ B ⊗₀ X} →
      trace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from)
      ≈ id {Y} ⊗₁ trace {X = X} f
    yanking :
      ∀ {X} → trace (braiding.⇒.η (X , X)) ≈ id

