{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Cartesian.Structure where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Monoidal as Monoidal
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Morphism as Morphisms
import Cheshire.Natural as Natural

open import Cheshire.Cartesian.Signature
open import Cheshire.Object.Signatures

open Category using (IsCategory)
open Monoidal using (IsMonoidal)

record IsCartesian {o ℓ} (e : 𝕃.t) {𝒬 : Quiver o ℓ} (𝒞 : Cartesian 𝒬) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  open Quiver 𝒬 using (_⇒_)
  open Cartesian 𝒞
  private instance
      _ = terminal; _ = products
  field
    ⦃ eq ⦄ : Equivalence 𝒬 e

    -- category
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
  open Morphisms.Reasoning isCategory

  -- cartesian
  field
    -- terminal
    !-unique : ∀ {A} → (f : A ⇒ ⊤) → ! ≈ f
    -- product
    project₁ : ∀ {A B C} {h : C ⇒ A} {i : C ⇒ B} → π₁ ∘ ⟨ h , i ⟩ ≈ h
    project₂ : ∀ {A B C} {h : C ⇒ A} {i : C ⇒ B} → π₂ ∘ ⟨ h , i ⟩ ≈ i
    unique :
      ∀ {A B C} {h : C ⇒ A × B} {i : C ⇒ A} {j : C ⇒ B} →
      π₁ ∘ h ≈ i → π₂ ∘ h ≈ j →
      ⟨ i , j ⟩ ≈ h

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

  ⟨⟩-congʳ :
    ∀ {f f′ : C ⇒ A} {g : C ⇒ B} →
    f ≈ f′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g ⟩
  ⟨⟩-congʳ pf = ⟨⟩-cong₂ pf refl

  ⟨⟩-congˡ :
    ∀ {f : C ⇒ A} {g g′ : C ⇒ B} →
    g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f , g′ ⟩
  ⟨⟩-congˡ pf = ⟨⟩-cong₂ refl pf

  ∘-distribʳ-⟨⟩ :
    ∀ {A B C D} {f : C ⇒ A} {g : C ⇒ B} {q : D ⇒ C} →
    ⟨ f , g ⟩ ∘ q ≈ ⟨ f ∘ q , g ∘ q ⟩
  ∘-distribʳ-⟨⟩ = ⟺ $ unique (pullˡ project₁) (pullˡ project₂)

  unique′ :
    ∀ {A B C} {h i : C ⇒ A × B} →
    π₁ ∘ h ≈ π₁ ∘ i → π₂ ∘ h ≈ π₂ ∘ i → h ≈ i
  unique′ eq₁ eq₂ = trans (sym (unique eq₁ eq₂)) g-η

  open Morphisms.Structures category
  open Morphisms.Bundles category

  ×-comm : ∀ {A B} → A × B ≅ B × A
  ×-comm = record
    { from = swap
    ; to = swap
    ; isIso = record
      { isoˡ = begin
        ⟨ π₂ , π₁ ⟩ ∘ ⟨ π₂ , π₁ ⟩                ≈⟨ ∘-distribʳ-⟨⟩ ⟩
        ⟨ π₂  ∘ ⟨ π₂ , π₁ ⟩ , π₁ ∘ ⟨ π₂ , π₁ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ project₂ project₁ ⟩
        ⟨ π₁ , π₂ ⟩                              ≈⟨ η ⟩
        id                                       ∎
      ; isoʳ = ∘-distribʳ-⟨⟩ ○ ⟨⟩-cong₂ project₂ project₁ ○ η
      }
    }

  ×-assoc : ∀ {X Y Z} → X × Y × Z ≅ (X × Y) × Z
  ×-assoc = record
    { from = assocʳ
    ; to = assocˡ
    ; isIso = record
        { isoˡ = begin
            ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
          ≈⟨ ∘-distribʳ-⟨⟩ ⟩
            ⟨ (π₁ ∘ π₁) ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
            , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
            ⟩
          ≈⟨ ⟨⟩-cong₂ (pullʳ project₁ ○ project₁) ∘-distribʳ-⟨⟩ ⟩
            ⟨ π₁
            , ⟨ (π₂ ∘ π₁) ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
              , π₂ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
              ⟩
            ⟩
          ≈⟨ ⟨⟩-congˡ (⟨⟩-cong₂ (pullʳ project₁ ○ project₂) project₂) ⟩
            ⟨ π₁
            , ⟨ π₁ ∘ π₂
              , π₂ ∘ π₂
              ⟩
            ⟩
          ≈⟨ ⟨⟩-congˡ g-η ⟩
            ⟨ π₁ , π₂ ⟩
          ≈⟨ η ⟩
            id
          ∎
        ; isoʳ = begin
              ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
            ≈⟨ ∘-distribʳ-⟨⟩ ⟩
              ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
              , (π₂ ∘ π₂) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
              ⟩
            ≈⟨ ⟨⟩-cong₂ ∘-distribʳ-⟨⟩ (pullʳ project₂ ○ project₂) ⟩
              ⟨ ⟨ π₁ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
                , (π₁ ∘ π₂) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
                ⟩
              , π₂
              ⟩
            ≈⟨ ⟨⟩-congʳ (⟨⟩-cong₂ project₁ (pullʳ project₂ ○ project₁)) ⟩
              ⟨ ⟨ π₁ ∘ π₁
                , π₂ ∘ π₁
                ⟩
              , π₂
              ⟩
            ≈⟨ ⟨⟩-congʳ g-η ⟩
              ⟨ π₁ , π₂ ⟩
            ≈⟨ η ⟩
              id
            ∎
        }
    }

  -- -- agda-categories BinaryProducts
  assocʳ∘assocˡ : assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
  assocʳ∘assocˡ = _≅_.isoʳ ×-assoc

  assocˡ∘assocʳ : assocˡ {A}{B}{C} ∘ assocʳ {A}{B}{C} ≈ id
  assocˡ∘assocʳ = _≅_.isoˡ ×-assoc

  π₁∘⁂ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} →
    π₁ ∘ (f ⁂ g) ≈ f ∘ π₁
  π₁∘⁂ {f = f} {g} = project₁

  π₂∘⁂ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} →
    π₂ ∘ (f ⁂ g) ≈ g ∘ π₂
  π₂∘⁂ {f = f} {g} = project₂

  ⁂-cong₂ :
    ∀ {f g : A ⇒ B} {h i : C ⇒ D} →
    f ≈ g → h ≈ i → f ⁂ h ≈ g ⁂ i
  ⁂-cong₂ {f = f} {g} {h} {i} f≈g h≈i = ⟨⟩-cong₂ (f≈g ⟩∘⟨refl) (h≈i ⟩∘⟨refl)

  ⁂∘⟨⟩ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} {f′ : X ⇒ A} {g′ : X ⇒ C} →
    (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g ∘ g′ ⟩
  ⁂∘⟨⟩ {f = f} {g} {f′} {g′} = begin
      ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ ⟨ f′ , g′ ⟩
    ≈⟨ ∘-distribʳ-⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ ⟨ f′ , g′ ⟩ , (g ∘ π₂) ∘ ⟨ f′ , g′ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ project₂) ⟩
      ⟨ f ∘ f′ , g ∘ g′ ⟩
    ∎

  first∘⟨⟩ :
    ∀ {f : A ⇒ X} {f′ : C ⇒ A} {g′ : C ⇒ B} →
    first f ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ {f = f} {f′} {g′} = begin
    first f ∘ ⟨ f′ , g′ ⟩ ≈⟨ ∘-distribʳ-⟨⟩ ⟩
    ⟨ (f ∘ π₁) ∘ ⟨ f′ , g′ ⟩ , π₂ ∘ ⟨ f′ , g′ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) project₂ ⟩
    ⟨ f ∘ f′ , g′ ⟩ ∎

  second∘⟨⟩ :
    ∀ {g : B ⇒ X} {f′ : C ⇒ A} {g′ : C ⇒ B} →
    second g ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ {g = g} {f′} {g′} = ∘-distribʳ-⟨⟩ ○ ⟨⟩-cong₂ project₁ (pullʳ project₂)

  ⁂∘⁂ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} {f′ : X ⇒ A} {g′ : Y ⇒ C} →
    (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
  ⁂∘⁂ {f = f} {g} {f′} {g′} = begin
      ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ ⟨ f′ ∘ π₁ , g′ ∘ π₂ ⟩
    ≈⟨ ∘-distribʳ-⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ ⟨ f′ ∘ π₁ , g′ ∘ π₂ ⟩ , (g ∘ π₂) ∘ ⟨ f′ ∘ π₁ , g′ ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ project₂) ⟩
      ⟨ f ∘ f′ ∘ π₁ , g ∘ g′ ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc assoc ⟨
      ⟨ (f ∘ f′) ∘ π₁ , (g ∘ g′) ∘ π₂ ⟩
    ∎

  ⟨⟩∘ :
    ∀ {f : C ⇒ A} {g : C ⇒ B} {h : X ⇒ C} →
    ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
  ⟨⟩∘ = ∘-distribʳ-⟨⟩

  first∘first :
    ∀ {f : B ⇒ C} {g : A ⇒ B} →
    ∀ {C} → first {C = C} f ∘ first g ≈ first (f ∘ g)
  first∘first {f = f} {g} = begin
    first f ∘ ⟨ g ∘ π₁ , π₂ ⟩ ≈⟨ first∘⟨⟩ ⟩
    ⟨ f ∘ g ∘ π₁ , π₂ ⟩       ≈⟨ ⟨⟩-congʳ assoc ⟨
    ⟨ (f ∘ g) ∘ π₁ , π₂ ⟩     ∎

  second∘second :
    ∀ {f : B ⇒ C} {g : A ⇒ B} →
    ∀ {A} → second {A = A} f ∘ second g ≈ second (f ∘ g)
  second∘second {f = f} {g} = second∘⟨⟩ ○ ⟺ (⟨⟩-congˡ assoc)

  first∘second :
    ∀ {f : A ⇒ B} {g : C ⇒ D} →
    first f ∘ second g ≈ f ⁂ g
  first∘second {f = f} {g} = first∘⟨⟩

  second∘first :
    ∀ {f : A ⇒ B} {g : C ⇒ D} →
    second f ∘ first g ≈ g ⁂ f
  second∘first {f = f} {g} = second∘⟨⟩

  first↔second :
    ∀ {f : A ⇒ B} {g : C ⇒ D} →
    first f ∘ second g ≈ second g ∘ first f
  first↔second = first∘⟨⟩ ○ ⟺ second∘⟨⟩

  firstid : ∀ {f : A ⇒ A} (g : A ⇒ C) → first {C = C} f ≈ id → f ≈ id
  firstid {f = f} g eq = begin
    f                   ≈⟨ introʳ project₁ ⟩
    f ∘ π₁ ∘ ⟨ id , g ⟩ ≈⟨ pullˡ fπ₁≈π₁ ⟩
    π₁ ∘ ⟨ id , g ⟩     ≈⟨ project₁ ⟩
    id                  ∎
    where fπ₁≈π₁ = begin
            f ∘ π₁       ≈⟨ project₁ ⟨
            π₁ ∘ first f ≈⟨ refl⟩∘⟨ eq ⟩
            π₁ ∘ id      ≈⟨ identityʳ ⟩
            π₁           ∎

  swap∘⟨⟩ :
    ∀ {f : C ⇒ A} {g : C ⇒ B} →
    swap ∘ ⟨ f , g ⟩ ≈ ⟨ g , f ⟩
  swap∘⟨⟩ {f = f} {g} = ∘-distribʳ-⟨⟩ ○ ⟨⟩-cong₂ project₂ project₁

  swap∘⁂ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} →
    swap ∘ (f ⁂ g) ≈ (g ⁂ f) ∘ swap
  swap∘⁂ {f = f} {g} = swap∘⟨⟩ ○ ⟺ ⁂∘⟨⟩

  swap∘swap : (swap {A}{B}) ∘ (swap {B}{A}) ≈ id
  swap∘swap = swap∘⟨⟩ ○ η

  swap-epi : IsEpi (swap {A} {B})
  swap-epi f g eq = introʳ swap∘swap ○ pullˡ eq ○ cancelʳ swap∘swap

  swap-mono : IsMono (swap {A} {B})
  swap-mono f g eq = introˡ swap∘swap ○ pullʳ eq ○ cancelˡ swap∘swap

  assocʳ∘⟨⟩ :
    ∀ {f : C ⇒ D} {g : C ⇒ A} {h : C ⇒ B} →
    assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈ ⟨ ⟨ f , g ⟩ , h ⟩
  assocʳ∘⟨⟩ {f = f} {g = g} {h = h} = begin
      assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ≈⟨ refl ⟩
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ≈⟨ ∘-distribʳ-⟨⟩ ⟩
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
      , (π₂ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
      ⟩
    ≈⟨ ⟨⟩-cong₂ ∘-distribʳ-⟨⟩ (pullʳ project₂) ⟩
      ⟨ ⟨ π₁        ∘ ⟨ f , ⟨ g , h ⟩ ⟩
        , (π₁ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
        ⟩
      , π₂ ∘ ⟨ g , h ⟩
      ⟩
    ≈⟨ ⟨⟩-cong₂ (⟨⟩-cong₂ project₁ (pullʳ project₂ ○ project₁)) project₂ ⟩
      ⟨ ⟨ f , g ⟩ , h ⟩
    ∎

  assocˡ∘⟨⟩ :
    ∀ {f : C ⇒ A} {g : C ⇒ B} {h : C ⇒ D} →
    assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩ ≈ ⟨ f , ⟨ g , h ⟩ ⟩
  assocˡ∘⟨⟩ {f = f} {g = g} {h = h} = begin
    assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩          ≈⟨ (refl⟩∘⟨ assocʳ∘⟨⟩) ⟨
    assocˡ ∘ assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈⟨ cancelˡ assocˡ∘assocʳ ⟩
    ⟨ f , ⟨ g , h ⟩ ⟩                   ∎

  assocʳ∘⁂ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} {h : X ⇒ Y} →
    assocʳ ∘ (f ⁂ (g ⁂ h)) ≈ ((f ⁂ g) ⁂ h) ∘ assocʳ
  assocʳ∘⁂ {f = f} {g = g} {h = h} = begin
      assocʳ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
    ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ ∘-distribʳ-⟨⟩ ⟩
      assocʳ ∘ ⟨ f ∘ π₁ , ⟨ (g ∘ π₁) ∘ π₂ , (h ∘ π₂) ∘ π₂ ⟩ ⟩
    ≈⟨ assocʳ∘⟨⟩ ⟩
      ⟨ ⟨ f ∘ π₁ , (g ∘ π₁) ∘ π₂ ⟩ , (h ∘ π₂) ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (⟨⟩-congˡ assoc) assoc ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈⟨ ⟨⟩-congʳ ⁂∘⟨⟩ ⟨
       ⟨ (f ⁂ g) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈⟨ ⁂∘⟨⟩ ⟨
      ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩ ∘ assocʳ
    ∎

  assocˡ∘⁂ :
    ∀ {f : A ⇒ B} {g : C ⇒ D} {h : X ⇒ Y} →
    assocˡ ∘ ((f ⁂ g) ⁂ h) ≈ (f ⁂ (g ⁂ h)) ∘ assocˡ
  assocˡ∘⁂ {f = f} {g = g} {h = h} = begin
      assocˡ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
    ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ ∘-distribʳ-⟨⟩ ⟩
      assocˡ ∘ ⟨ ⟨ (f ∘ π₁) ∘ π₁ , (g ∘ π₂) ∘ π₁ ⟩ , h ∘ π₂ ⟩
    ≈⟨ assocˡ∘⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ (g ∘ π₂) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc (⟨⟩-congʳ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ g ∘ π₂ ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-congˡ ⁂∘⟨⟩ ⟨
      ⟨ f ∘ π₁ ∘ π₁ , (g ⁂ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈⟨ ⁂∘⟨⟩ ⟨
      ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩ ∘ assocˡ
    ∎

  Δ∘ :
    ∀ {f : A ⇒ B} →
    Δ ∘ f ≈ ⟨ f , f ⟩
  Δ∘ {f = f} = ∘-distribʳ-⟨⟩ ○ ⟨⟩-cong₂ identityˡ identityˡ

  ⁂∘Δ :
    ∀ {f : A ⇒ B} {g : A ⇒ D} →
    (f ⁂ g) ∘ Δ ≈ ⟨ f , g ⟩
  ⁂∘Δ {f = f} {g} =
    ∘-distribʳ-⟨⟩ ○ ⟨⟩-cong₂ (pullʳ project₁ ○ identityʳ) (pullʳ project₂ ○ identityʳ)

  -- Monoidal
  private
    open Commutation
    open Monoidal.Signature monoidal using (_⊗₀_; _⊗₁_)
    open Natural using (NaturalIsomorphism)
    open Morphisms.Signatures 𝒬
    cat : Category.t e 𝒬
    cat = record { signature = category; structure = isCategory }
    α⇒ = assocˡ

    ⊤×A≅A : ⊤ × A ≅ A
    ⊤×A≅A = record
      { from = π₂
      ; to = ⟨ ! , id ⟩
      ; isIso = record
          { isoˡ = begin
               ⟨ ! , id ⟩ ∘ π₂ ≈⟨ unique !-unique₂ (cancelˡ project₂) ⟨
               ⟨ π₁ , π₂ ⟩     ≈⟨ η ⟩
               id ∎
          ; isoʳ = project₂
          }
      }

    A×⊤≅A : A × ⊤ ≅ A
    A×⊤≅A = record
      { _⇔_ A×⊤⇔A
      ; isIso = record
          { isoˡ = begin
              ⟨ id , ! ⟩ ∘ π₁ ≈⟨ unique (cancelˡ project₁) !-unique₂ ⟨
              ⟨ π₁ , π₂ ⟩     ≈⟨ η ⟩
              id ∎
          ; isoʳ = project₁
          }
      }

    ⊤×--id-isIso : Natural.IsIsomorphism isCategory ⊤×-
    ⊤×--id-isIso = record
      { F⇒G = record { commute = λ _ → project₂ }
      ; F⇐G = record { commute = λ f → begin
          ⟨ ! , id ⟩ ∘ f                                     ≈⟨ ⟨⟩∘ ⟩
          ⟨ ! ∘ f , id ∘ f ⟩                                 ≈⟨ ⟨⟩-cong₂ (⟺ (!-unique (! ∘ f))) identityˡ ⟩
          ⟨ ! , f ⟩                                          ≈⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟨
          ⟨ id ∘ ! , f ∘ id ⟩                                ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ project₂) ⟨
          ⟨ (id ∘ π₁) ∘ ⟨ ! , id ⟩ , (f ∘ π₂) ∘ ⟨ ! , id ⟩ ⟩ ≈⟨ ⟨⟩∘ ⟨
          ⟨ id ∘ π₁ , f ∘ π₂ ⟩ ∘ ⟨ ! , id ⟩                  ∎
      }
      ; iso = λ _ → _≅_.isIso ⊤×A≅A
      }

    ⊤×--id : NaturalIsomorphism cat (⊤ ×-) Morphism.id
    ⊤×--id = record { signature = ⊤×-; structure = ⊤×--id-isIso }

    -×⊤-id-isIso : Natural.IsIsomorphism isCategory -×⊤
    -×⊤-id-isIso = record
      { F⇒G = record { commute = λ _ → project₁ }
      ; F⇐G = record { commute = λ f → begin
          ⟨ id , ! ⟩ ∘ f                                     ≈⟨ ⟨⟩∘ ⟩
          ⟨ id ∘ f , ! ∘ f ⟩                                 ≈⟨ ⟨⟩-cong₂ identityˡ (⟺ (!-unique (! ∘ f))) ⟩
          ⟨ f , ! ⟩                                          ≈⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟨
          ⟨ f ∘ id , id ∘ ! ⟩                                ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ project₂) ⟨
          ⟨ (f ∘ π₁) ∘ ⟨ id , ! ⟩ , (id ∘ π₂) ∘ ⟨ id , ! ⟩ ⟩ ≈⟨ ⟨⟩∘ ⟨
          ⟨ f ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ id , ! ⟩                  ∎
      }
      ; iso = λ x → _≅_.isIso A×⊤≅A
      }

    -×⊤-id : NaturalIsomorphism cat (-× ⊤) Morphism.id
    -×⊤-id = record { signature = -×⊤; structure = -×⊤-id-isIso }

    pentagon :
      ∀ {X Y Z W} →
      [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒   X ⊗₀  Y  ⊗₀ Z  ⊗₀ W ]⟨
        α⇒ ⊗₁ id             ⇒⟨ (X ⊗₀  Y  ⊗₀ Z) ⊗₀ W ⟩
        α⇒                   ⇒⟨  X ⊗₀ (Y  ⊗₀ Z) ⊗₀ W ⟩
        id ⊗₁ α⇒
      ≈ α⇒                   ⇒⟨ (X ⊗₀  Y) ⊗₀ Z  ⊗₀ W ⟩
        α⇒
      ⟩
    pentagon = begin
        (id ⁂ α⇒) ∘ α⇒ ∘ (α⇒ ⁂ id)
      ≈⟨ ⟨⟩-congʳ identityˡ ⟩∘⟨ refl ⟩∘⟨ ⟨⟩-congˡ identityˡ ⟩
        second α⇒ ∘ α⇒ ∘ first α⇒
        -- second α⇒ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ first α⇒
      ≈⟨ pullˡ second∘⟨⟩ ⟩
        ⟨ π₁ ∘ π₁ , α⇒ ∘ first π₂ ⟩ ∘ first α⇒
      ≈⟨ ∘-distribʳ-⟨⟩ ⟩
        ⟨ (π₁ ∘ π₁) ∘ first α⇒ , (α⇒ ∘ first π₂) ∘ first α⇒ ⟩
      ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ first∘first) ⟩
        ⟨ π₁ ∘ α⇒ ∘ π₁ , α⇒ ∘ first (π₂ ∘ α⇒) ⟩
      ≈⟨ ⟨⟩-cong₂ (pullˡ project₁ ○ assoc) (refl⟩∘⟨ ⟨⟩-congʳ (project₂ ⟩∘⟨refl)) ⟩
        ⟨ π₁ ∘ π₁ ∘ π₁ , α⇒ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ π₁ , π₂ ⟩ ⟩
      ≈⟨ ⟨⟩-congˡ (refl⟩∘⟨ ⟨⟩-congʳ ∘-distribʳ-⟨⟩) ⟩
        ⟨ π₁ ∘ π₁ ∘ π₁ , α⇒ ∘ ⟨ ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩ , π₂ ⟩ ⟩
      ≈⟨ ⟨⟩-congˡ assocˡ∘⟨⟩ ⟩
        ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ (π₂ ∘ π₁) ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
      ≈⟨ ⟨⟩-congˡ (⟨⟩-cong₂ (pullʳ project₁ ○ ⟺ assoc) project₂) ⟨
        ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ (π₂ ∘ π₁) ∘ α⇒ , π₂ ∘ α⇒ ⟩ ⟩
      ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) ∘-distribʳ-⟨⟩ ⟨
        ⟨ (π₁ ∘ π₁) ∘ α⇒ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ α⇒ ⟩
      ≈⟨ ∘-distribʳ-⟨⟩ ⟨
        α⇒ ∘ α⇒
      ∎

  isMonoidal : IsMonoidal e monoidal
  isMonoidal = record
    { IsCategory isCategory
    ; unitorˡ = ⊤×A≅A
    ; unitorʳ = A×⊤≅A
    ; associator = ≅.sym isCategory ×-assoc
    ; unitorˡ-commute-from = project₂
    ; unitorˡ-commute-to = let open NaturalIsomorphism ⊤×--id in ⇐.commute _
    ; unitorʳ-commute-from = project₁
    ; unitorʳ-commute-to = let open NaturalIsomorphism -×⊤-id in ⇐.commute _
    ; assoc-commute-from = assocˡ∘⁂
    ; assoc-commute-to = assocʳ∘⁂
    ; triangle = begin
        (id ⁂ π₂) ∘ assocˡ
      ≈⟨ ⁂∘⟨⟩ ⟩
        ⟨ id ∘ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ≈⟨ ⟨⟩-cong₂ (pullˡ identityˡ) (project₂ ○ ⟺ identityˡ) ⟩
        π₁ ⁂ id
      ∎
    ; pentagon = pentagon
    }
