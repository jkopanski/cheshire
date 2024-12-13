{-# OPTIONS --safe #-}

module Cheshire.Structures.Core where

open import Cheshire.Core
open import Cheshire.Signatures
open import Cheshire.Object.Signatures

record IsCategory {o ℓ} (e : 𝕃.t) {𝒬 : Quiver o ℓ} (𝒞 : Category 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Quiver 𝒬 using (_⇒_)
  open Category 𝒞
  field
    ⦃ eq ⦄ : Equivalence 𝒬 e

    assoc :
      ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  ∘-resp-≈ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
  ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl

  ∘-resp-≈ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
  ∘-resp-≈ʳ pf = ∘-resp-≈ refl pf

  module HomReasoning {A B : 𝒬 .Ob} where
    open Rel₂.SetoidReasoning (setoid {A = A} {B = B}) public

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_
    infixl 5 _⟩∘⟨refl
    _⟩∘⟨_ :
      ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} →
      f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    _⟩∘⟨_ = ∘-resp-≈

    refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≈ i → f ∘ g ≈ f ∘ i
    refl⟩∘⟨_ = refl ⟩∘⟨_

    _⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≈ h → f ∘ g ≈ h ∘ g
    _⟩∘⟨refl = _⟩∘⟨ refl

    infix 2 ⟺
    infixr 3 _○_
    ⟺ : {f g : A ⇒ B} → f ≈ g → g ≈ f
    ⟺ = sym
    _○_ : {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    _○_ = trans

  module Commutation where

    -- A -- f --> B
    -- |          |
    -- g          h
    -- |          |
    -- V          V
    -- C -- i --> D
    CommutativeSquare : {A B C D : 𝒬 .Ob} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set e
    CommutativeSquare f g h i = h ∘ f ≈ i ∘ g

    infix 1 [_⇒_]⟨_≈_⟩
    [_⇒_]⟨_≈_⟩ : ∀ (A B : 𝒬 .Ob) → A ⇒ B → A ⇒ B → Set e
    [ A ⇒ B ]⟨ f ≈ g ⟩ = f ≈ g

    infixl 2 connect
    connect : ∀ {A C : 𝒬 .Ob} (B : 𝒬 .Ob) → A ⇒ B → B ⇒ C → A ⇒ C
    connect B f g = g ∘ f

    syntax connect B f g = f ⇒⟨ B ⟩ g

