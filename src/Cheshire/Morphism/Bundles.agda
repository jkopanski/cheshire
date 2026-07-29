{-# OPTIONS --safe #-}

open import Cheshire.Core
import Cheshire.Category.Signature as Category renaming (Category to t)

module Cheshire.Morphism.Bundles
  {o ℓ} {𝒬 : Quiver o ℓ} (𝒞 : Category.t 𝒬)
  where

import Data.Product as ×

import Cheshire.Morphism.Signatures 𝒬 as Signatures
import Cheshire.Morphism.Structures 𝒞 as Structures
import Cheshire.Morphism.Reasoning as MorphismReasoning

open import Cheshire.Category.Structure using (IsCategory)

open × using (Σ; Σ-syntax)
open Category.t 𝒞
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

≅-is-Iso : ⦃ _ : Equivalence 𝒬 e ⦄ → ∀ {A B : 𝒬 .Ob} → A ≅ B → Iso A B
≅-is-Iso ≅ = record { from = iso.from; to = iso.to } , iso.isIso
  where module iso = _≅_ ≅

Iso-is-≅ : ⦃ _ : Equivalence 𝒬 e ⦄ → ∀ {A B : 𝒬 .Ob} → Iso A B → A ≅ B
Iso-is-≅ (i , isIso) = record { _⇔_ i; isIso = isIso }

≅-is-⇔ : ⦃ _ : Equivalence 𝒬 e ⦄ → ∀ {A B : 𝒬 .Ob} → A ≅ B → A ⇔ B
≅-is-⇔ = proj₁ ⊙ ≅-is-Iso

Iso-is-⇔ : ⦃ _ : Equivalence 𝒬 e ⦄ → ∀ {A B : 𝒬 .Ob} → Iso A B → A ⇔ B
Iso-is-⇔ = proj₁

module _ {eq : Equivalence 𝒬 e} (isC : IsCategory eq 𝒞) where

  private instance _ = eq
  open IsCategory isC

  private
    ≅-refl : Rel₂.Reflexive _≅_
    ≅-refl = record
      { from = id
      ; to = id
      ; isIso = record
          { isoˡ = identityˡ
          ; isoʳ = identityˡ
          }
      }

    ≅-sym : Rel₂.Symmetric _≅_
    ≅-sym A≅B = record
      { from = to
      ; to = from
      ; isIso = record
          { isoˡ = isoʳ
          ; isoʳ = isoˡ
          }
      } where open _≅_ A≅B

    ≅-trans : Rel₂.Transitive _≅_
    ≅-trans A≅B B≅C = record
      { from = from B≅C ∘ from A≅B
      ; to = to A≅B ∘ to B≅C
      ; isIso = record
          { isoˡ = begin
              (to A≅B ∘ to B≅C) ∘ from B≅C ∘ from A≅B ≈⟨ cancelInner (isoˡ B≅C) ⟩
              to A≅B ∘ from A≅B                       ≈⟨ isoˡ A≅B ⟩
              id                                      ∎
          ; isoʳ = begin
              (from B≅C ∘ from A≅B) ∘ to A≅B ∘ to B≅C ≈⟨ cancelInner (isoʳ A≅B) ⟩
              from B≅C ∘ to B≅C                       ≈⟨ isoʳ B≅C ⟩
              id                                      ∎
          }
      } where open _≅_
              open HomReasoning
              open MorphismReasoning isC

  ≅-isEquivalence : Rel₂.IsEquivalence _≅_
  ≅-isEquivalence = record
    { refl = ≅-refl
    ; sym = ≅-sym
    ; trans = ≅-trans
    }

module ≅ {e} {eq : Equivalence 𝒬 e} (isC : IsCategory eq 𝒞) =
  Rel₂.IsEquivalence (≅-isEquivalence isC)
