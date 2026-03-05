{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Signatures

module Cheshire.Structures where

import Cheshire.Category.Structure as IsCategory renaming (IsCategory to t)
import Cheshire.Morphism.Bundles as Morphisms
import Cheshire.Morphism.Reasoning as Reasoning

open import Cheshire.Morphism.Structures using (IsEpi; IsMono)
open import Cheshire.Object.Signatures

open IsCategory public hiding (t)

record IsCartesian {o ℓ} (e : 𝕃.t) {𝒬 : Quiver o ℓ} (𝒞 : Cartesian 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Quiver 𝒬 using (_⇒_)
  open Cartesian 𝒞
  private instance
      _ = terminal; _ = products
  field
    ⦃ eq ⦄ : Equivalence 𝒬 e

    -- terminal
    !-unique : ∀ {A} → (f : A ⇒ ⊤) → ! ≈ f
    -- product
    project₁ : ∀ {A B C} {h : C ⇒ A} {i : C ⇒ B} → π₁ ∘ ⟨ h , i ⟩ ≈ h
    project₂ : ∀ {A B C} {h : C ⇒ A} {i : C ⇒ B} → π₂ ∘ ⟨ h , i ⟩ ≈ i
    unique :
      ∀ {A B C} {h : C ⇒ A × B} {i : C ⇒ A} {j : C ⇒ B} →
      π₁ ∘ h ≈ i → π₂ ∘ h ≈ j →
      ⟨ i , j ⟩ ≈ h

    assoc :
      ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
      (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  isCategory : IsCategory.t e category
  isCategory = record
    { assoc = assoc; identityˡ = identityˡ; identityʳ = identityʳ; ∘-resp-≈ = ∘-resp-≈ }

  open IsCategory.t isCategory using (module HomReasoning)
  open HomReasoning
  open Reasoning isCategory

  private
    variable
      A B C D X Y : 𝒬 .Ob

  -- agda-categories Terminal
  !-unique₂ : ∀ {f g : A ⇒ ⊤} → f ≈ g
  !-unique₂ {f = f} {g} = begin
    f ≈˘⟨ !-unique f ⟩
    ! ≈⟨ !-unique g ⟩
    g ∎

  ⊤-id : (f : ⊤ ⇒ ⊤) → f ≈ id
  ⊤-id _ = !-unique₂

  -- agda-categories Product
  g-η :
    ∀ {A B C} {h : C ⇒ A × B} →
    ⟨ π₁ ∘ h , π₂ ∘ h ⟩ ≈ h
  g-η = unique refl refl

  η : ∀ {A B} → ⟨ π₁ , π₂ ⟩ ≈ id {A × B}
  η = unique identityʳ identityʳ

  ⟨⟩-cong₂ :
    ∀ {A B C} {f f′ : C ⇒ A} {g g′ : C ⇒ B} →
    f ≈ f′ → g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ f≈f′ g≈g′ = unique (project₁ ○ ⟺ f≈f′) (project₂ ○ ⟺ g≈g′)

  ∘-distribʳ-⟨⟩ :
    ∀ {A B C D} {f : C ⇒ A} {g : C ⇒ B} {q : D ⇒ C} →
    ⟨ f , g ⟩ ∘ q ≈ ⟨ f ∘ q , g ∘ q ⟩
  ∘-distribʳ-⟨⟩ = ⟺ $ unique (pullˡ project₁) (pullˡ project₂)

  unique′ :
    ∀ {A B C} {h i : C ⇒ A × B} →
    π₁ ∘ h ≈ π₁ ∘ i → π₂ ∘ h ≈ π₂ ∘ i → h ≈ i
  unique′ eq₁ eq₂ = trans (sym (unique eq₁ eq₂)) g-η

  open Morphisms category

  -- -- agda-categories BinaryProducts
  -- assocʳ∘assocˡ : assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
  -- assocʳ∘assocˡ = {!!}

  -- assocˡ∘assocʳ : assocˡ {A}{B}{C} ∘ assocʳ {A}{B}{C} ≈ id
  -- assocˡ∘assocʳ = {!!}

  -- ⟨⟩-congʳ :
  --   ∀ {f f′ : C ⇒ A} {g : C ⇒ B} →
  --   f ≈ f′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g ⟩
  -- ⟨⟩-congʳ pf = {!!}

  -- ⟨⟩-congˡ :
  --   ∀ {f : C ⇒ A} {g g′ : C ⇒ B} →
  --   g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f , g′ ⟩
  -- ⟨⟩-congˡ pf = {!!}

  -- π₁∘⁂ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} →
  --   π₁ ∘ (f ⁂ g) ≈ f ∘ π₁
  -- π₁∘⁂ {f = f} {g} = project₁

  -- π₂∘⁂ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} →
  --   π₂ ∘ (f ⁂ g) ≈ g ∘ π₂
  -- π₂∘⁂ {f = f} {g} = project₂

  -- ⁂-cong₂ :
  --   ∀ {f g : A ⇒ B} {h i : C ⇒ D} →
  --   f ≈ g → h ≈ i → f ⁂ h ≈ g ⁂ i
  -- ⁂-cong₂ = {!!}

  -- ⁂∘⟨⟩ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} {f′ : X ⇒ A} {g′ : X ⇒ C} →
  --   (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g ∘ g′ ⟩
  -- ⁂∘⟨⟩ = {!!}

  -- first∘⟨⟩ :
  --   ∀ {f : A ⇒ X} {f′ : C ⇒ A} {g′ : C ⇒ B} →
  --   first f ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g′ ⟩
  -- first∘⟨⟩ = {!!}

  -- second∘⟨⟩ :
  --   ∀ {g : B ⇒ X} {f′ : C ⇒ A} {g′ : C ⇒ B} →
  --   second g ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f′ , g ∘ g′ ⟩
  -- second∘⟨⟩ = {!!}

  -- ⁂∘⁂ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} {f′ : X ⇒ A} {g′ : Y ⇒ C} →
  --   (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
  -- ⁂∘⁂ = {!!}

  -- ⟨⟩∘ :
  --   ∀ {f : C ⇒ A} {g : C ⇒ B} {h : X ⇒ C} →
  --   ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
  -- ⟨⟩∘ = {!!}

  -- first∘first :
  --   ∀ {f : B ⇒ C} {g : A ⇒ B} →
  --   ∀ {C} → first {C = C} f ∘ first g ≈ first (f ∘ g)
  -- first∘first = {!!}

  -- second∘second :
  --   ∀ {f : B ⇒ C} {g : A ⇒ B} →
  --   ∀ {A} → second {A = A} f ∘ second g ≈ second (f ∘ g)
  -- second∘second = {!!}

  -- first∘second :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} →
  --   first f ∘ second g ≈ f ⁂ g
  -- first∘second {f = f} {g = g} = {!!}

  -- second∘first :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} →
  --   second f ∘ first g ≈ g ⁂ f
  -- second∘first {f = f} {g = g} = {!!}

  -- first↔second :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} →
  --   first f ∘ second g ≈ second g ∘ first f
  -- first↔second = {!!}

  -- firstid : ∀ {f : A ⇒ A} (g : A ⇒ C) → first {C = C} f ≈ id → f ≈ id
  -- firstid {f = f} g eq = {!!}

  -- swap∘⟨⟩ :
  --   ∀ {f : C ⇒ A} {g : C ⇒ B} →
  --   swap ∘ ⟨ f , g ⟩ ≈ ⟨ g , f ⟩
  -- swap∘⟨⟩ {f = f} {g = g} = {!!}

  -- swap∘⁂ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} →
  --   swap ∘ (f ⁂ g) ≈ (g ⁂ f) ∘ swap
  -- swap∘⁂ {f = f} {g = g} = {!!}

  -- swap∘swap : (swap {A}{B}) ∘ (swap {B}{A}) ≈ id
  -- swap∘swap = {!!}

  -- swap-epi : IsEpi category (swap {A} {B})
  -- swap-epi f g eq = {!!}

  -- swap-mono : IsMono category (swap {A} {B})
  -- swap-mono f g eq = {!!}

  -- assocʳ∘⟨⟩ :
  --   ∀ {f : C ⇒ D} {g : C ⇒ A} {h : C ⇒ B} →
  --   assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈ ⟨ ⟨ f , g ⟩ , h ⟩
  -- assocʳ∘⟨⟩ {f = f} {g = g} {h = h} = {!!}

  -- assocˡ∘⟨⟩ :
  --   ∀ {f : C ⇒ A} {g : C ⇒ B} {h : C ⇒ D} →
  --   assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩ ≈ ⟨ f , ⟨ g , h ⟩ ⟩
  -- assocˡ∘⟨⟩ {f = f} {g = g} {h = h} = {!!}

  -- assocʳ∘⁂ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} {h : X ⇒ Y} →
  --   assocʳ ∘ (f ⁂ (g ⁂ h)) ≈ ((f ⁂ g) ⁂ h) ∘ assocʳ
  -- assocʳ∘⁂ {f = f} {g = g} {h = h} = {!!}

  -- assocˡ∘⁂ :
  --   ∀ {f : A ⇒ B} {g : C ⇒ D} {h : X ⇒ Y} →
  --   assocˡ ∘ ((f ⁂ g) ⁂ h) ≈ (f ⁂ (g ⁂ h)) ∘ assocˡ
  -- assocˡ∘⁂ {f = f} {g = g} {h = h} = {!!}

  -- Δ∘ :
  --   ∀ {f : A ⇒ B} →
  --   Δ ∘ f ≈ ⟨ f , f ⟩
  -- Δ∘ {f = f} = {!!}

  -- ⁂∘Δ :
  --   ∀ {f : A ⇒ B} {g : A ⇒ D} →
  --   (f ⁂ g) ∘ Δ ≈ ⟨ f , g ⟩
  -- ⁂∘Δ {f = f} {g = g} = {!!}

  -- ×-comm : ∀ {A B} → A × B ≅ B × A
  -- ×-comm = record
  --   { from = swap
  --   ; to = swap
  --   ; isIso = record
  --     { isoˡ = begin
  --       swap ∘ swap ≈⟨ {!!} ⟩
  --       id ∎
  --     ; isoʳ = {!!}
  --     }
  --   }

  -- ×-assoc : ∀ {X Y Z} → X × Y × Z ≅ (X × Y) × Z
  -- ×-assoc = {!!}
