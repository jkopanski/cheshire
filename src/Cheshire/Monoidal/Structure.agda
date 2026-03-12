{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Structure where

import Cheshire.Morphism.Bundles as MorphismBundles
import Cheshire.Morphism.Reasoning as MorphismReasoning
import Cheshire.Natural as Natural
open import Cheshire.Category.Structure
open import Cheshire.Monoidal.Signature

private
  variable
    o ℓ : 𝕃.t

record IsMonoidal (e : 𝕃.t) {𝒬 : Quiver o ℓ} (ℳ : Monoidal 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Quiver 𝒬 using (_⇒_)
  open Monoidal ℳ
  open MorphismBundles category
  field
    ⦃ eq ⦄ : Equivalence 𝒬 e

  -- Category
  field
    assoc :
      ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  isCategory : IsCategory e category
  isCategory = record
    { assoc = assoc; identityˡ = identityˡ; identityʳ = identityʳ; ∘-resp-≈ = ∘-resp-≈ }

  open IsCategory isCategory using (module Commutation; module HomReasoning)
  open HomReasoning
  open Commutation
  open MorphismReasoning isCategory

  -- Monoidal
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
  open Quiver 𝒬 using (_⇒_)
  open Braided ℳ renaming (braiding to signature)
  open MorphismBundles category
  field
    ⦃ eq ⦄ : Equivalence 𝒬 e

  -- Category
  field
    assoc :
      ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  isCategory : IsCategory e category
  isCategory = record
    { assoc = assoc; identityˡ = identityˡ; identityʳ = identityʳ; ∘-resp-≈ = ∘-resp-≈ }

  open IsCategory isCategory using (module Commutation; module HomReasoning)
  open HomReasoning
  open Commutation
  open MorphismReasoning isCategory

  -- Monoidal
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

  isMonoidal : IsMonoidal e monoidal
  isMonoidal = record
    { IsCategory isCategory; unitorˡ = unitorˡ; unitorʳ = unitorʳ; associator = associator
    ; unitorˡ-commute-from = unitorˡ-commute-from
    ; unitorˡ-commute-to = unitorˡ-commute-to
    ; unitorʳ-commute-from = unitorʳ-commute-from
    ; unitorʳ-commute-to = unitorʳ-commute-to
    ; assoc-commute-from = assoc-commute-from
    ; assoc-commute-to = assoc-commute-to
    ; triangle = triangle
    ; pentagon = pentagon
    }

  -- braided
  field
    braiding-isIso : Natural.IsIsomorphism isCategory signature

  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = signature.⇒.η (X , Y)

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
