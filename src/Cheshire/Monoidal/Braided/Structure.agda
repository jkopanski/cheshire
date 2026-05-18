{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Monoidal.Braided.Structure where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Monoidal as Monoidal renaming (IsMonoidal to Structure)
import Cheshire.Monoidal.Braided.Signature as Braided renaming (Braided to t)
import Cheshire.Morphism as Morphisms
import Cheshire.Natural as Natural

private
  variable
    o ℓ e : 𝕃.t
    𝒬 : Quiver o ℓ


record IsBraided
  {eq : Equivalence 𝒬 e}
  {𝒞 : Category.Signature 𝒬}
  (isCategory : Category.Structure eq 𝒞)
  {ℳ : Monoidal.Signature 𝒞}
  (ℬ : Braided.t ℳ)
    : Set (𝕃.levelOfTerm ℬ ⊔ 𝕃.suc e) where
  field
    isMonoidal : Monoidal.Structure isCategory ℳ

  private instance _ = eq
  open Category.Signature 𝒞
  open Monoidal.Signature ℳ
  open Braided.t ℬ
  open Category.Structure isCategory
  open Monoidal.Structure isMonoidal
  open HomReasoning
  open Commutation
  open Morphisms.Reasoning isCategory

  field
    braiding-isIso : Natural.IsIsomorphism isCategory braiding

  module braiding-isIso = Natural.IsIsomorphism braiding-isIso

  σ = braiding-isIso.FX≅GX

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

