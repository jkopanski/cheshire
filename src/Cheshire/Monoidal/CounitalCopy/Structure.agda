{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.CounitalCopy.Structure where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided as Braided renaming (IsBraided to Structure)
import Cheshire.Monoidal.CounitalCopy.Signature as CounitalCopy renaming (CounitalCopy to t)

private
  variable
    o ℓ e : 𝕃.t
    𝒬 : Quiver o ℓ


record IsCounitalCopy
  {eq : Equivalence 𝒬 e}
  {𝒞 : Category.Signature 𝒬}
  {isCategory : Category.Structure eq 𝒞}
  {ℳ : Monoidal.Signature 𝒞}
  (isMonoidal : Monoidal.Structure isCategory ℳ)
  (ℬ : Braided.Signature ℳ)
  (𝒞𝒞 : CounitalCopy.t ℳ)
    : Set (𝕃.levelOfTerm 𝒞 ⊔ 𝕃.suc e) where
  private instance _ = eq
  open Category.Signature 𝒞
  open Monoidal.Signature ℳ
  open CounitalCopy.t 𝒞𝒞
  open Monoidal.Structure isMonoidal
  open Braided.Signature ℬ

  field
    natural : ∀ {A B} (f : A ⇒ B) → Δ ∘ f ≈ (f ⊗₁ f) ∘ Δ
    inverse₁ : Δ ∘ λ⇒ ≈ id
    inverse₂ : λ⇒ ∘ Δ ≈ id
    cocommutative : ∀ {A} → σ⇒ ∘ Δ ≈ Δ {A}
    preserves : ∀ {X Y} → α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ ((σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (Δ ⊗₁ Δ) ≈ Δ {X ⊗₀ Y}
