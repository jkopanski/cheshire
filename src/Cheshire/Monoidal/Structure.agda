{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Structure where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Morphism as Morphisms
open import Cheshire.Monoidal.Signature

private
  variable
    o ℓ e : 𝕃.t
    𝒬 : Quiver o ℓ
    𝒞 : Category.Signature 𝒬
    ℳ : Monoidal 𝒞

record IsMonoidal
  {eq : Equivalence 𝒬 e}
  (isCategory : Category.Structure eq 𝒞)
  (ℳ : Monoidal 𝒞)
    : Set (𝕃.levelOfTerm ℳ ⊔ 𝕃.suc e) where
  no-eta-equality
  open Category.Signature 𝒞
  open Monoidal ℳ
  open Category.Structure isCategory
  open HomReasoning
  open Commutation
  open Morphisms.Bundles 𝒞
  private instance _ = eq

  field
    unitorˡ    : ∀ {X} → unit ⊗₀ X ≅ X
    unitorʳ    : ∀ {X} → X ⊗₀ unit ≅ X
    associator : ∀ {X Y Z} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

  module unitorˡ {X} = _≅_ (unitorˡ {X = X})
  module unitorʳ {X} = _≅_ (unitorʳ {X = X})
  module associator {X} {Y} {Z} = _≅_ (associator {X} {Y} {Z})

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
