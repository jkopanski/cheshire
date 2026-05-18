{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Traced.Structure where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided.Signature as Braided renaming (Braided to t)
import Cheshire.Monoidal.Traced.Signature as Traced renaming (Traced to t)

private
  variable
    o ℓ e : 𝕃.t
    𝒬 : Quiver o ℓ


record IsTraced
  {eq : Equivalence 𝒬 e}
  {𝒞 : Category.Signature 𝒬}
  {isCategory : Category.Structure eq 𝒞}
  {ℳ : Monoidal.Signature 𝒞}
  (isMonoidal : Monoidal.Structure isCategory ℳ)
  (ℬ : Braided.t ℳ) (𝒯 : Traced.t ℳ)
    : Set (𝕃.levelOfTerm 𝒯 ⊔ 𝕃.suc e) where
  no-eta-equality
  open Traced.t 𝒯
  open Braided.t ℬ
  open Monoidal.Signature ℳ
  open Monoidal.Structure isMonoidal
  open Category.Signature 𝒞
  private instance _ = eq

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

