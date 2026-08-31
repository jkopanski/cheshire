{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism where

import Data.Product as ×
open import Relation.Binary.PropositionalEquality.Subst.Properties
  using (module Shorthands; module Transport; module TransportMor; module TransportOverQ)
import Cheshire.Cartesian.Signature as Cartesian renaming (Cartesian to t)

module Category where
  open import Cheshire.Category.Signature public renaming (Category to Signature)
  open import Cheshire.Category.Bundle public renaming (Category to t)

open import Cheshire.Homomorphism.Signatures public
open import Cheshire.Homomorphism.Structures public
open import Cheshire.Homomorphism.Bundles public

-- Copied from agda-categories:
-- https://agda.github.io/agda-categories/Data.Quiver.Morphism.html#2527
-- which is licensed under the MIT license.
--   Copyright (c) 2019 Agda Github Community

open × using (Σ-syntax)
open Rel₂ using (_≡_; Reflexive; Symmetric; Transitive)

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : 𝕃.t

infix 4 _≃_
record _≃_
  {𝒬 : Quiver o ℓ} {𝒬′ : Quiver o′ ℓ′}
  ⦃ eq : Equivalence 𝒬′ e′ ⦄
  (ℳ ℳ′ : Morphism 𝒬 𝒬′)
  : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module M  = Morphism ℳ
    module M′ = Morphism ℳ′
  open Shorthands (𝒬′ .Hom)

  field
    F₀≡ : ∀ {X} → M.₀ X ≡ M′.₀ X
    F₁≡ : ∀ {A B} {f : 𝒬 .Hom A B} → M.₁ f ▸ F₀≡ ≈ F₀≡ ◂ M′.₁ f

module _
  {𝒬 : Quiver o ℓ} {𝒬′ : Quiver o ℓ}
  -- {e}  ⦃ eq  : Equivalence 𝒬  e  ⦄
  {e} ⦃ eq : Equivalence 𝒬′ e ⦄
  where
  open _≃_
  -- open Equivalence eq

  private
    open EdgeReasoning
    open Transport (𝒬′ .Hom)
    open TransportOverQ (𝒬′ .Hom) (eq ._≈_)

    ≃-refl : Reflexive {A = Morphism 𝒬 𝒬′} _≃_
    ≃-refl = record { F₀≡ = ≡-refl; F₁≡ = refl }

    ≃-sym : Symmetric {A = Morphism 𝒬 𝒬′} _≃_
    ≃-sym {x} {y} x≃y = record
      { F₀≡ = ≡-sym e₁
      ; F₁≡ = λ {_ _ f} →
        begin
          F₁ y f ▸ ≡-sym e₁
        ≡⟨ ≡-cong (_◂ (F₁ y f ▸ ≡-sym e₁)) (Rel₂.trans-symˡ e₁) ⟨
          ≡-trans (≡-sym e₁) e₁ ◂ (F₁ y f ▸ ≡-sym e₁)
        ≡⟨ ◂-assocˡ (≡-sym e₁) (F₁ y f ▸ ≡-sym e₁) ⟨
          ≡-sym e₁ ◂ e₁ ◂ (F₁ y f ▸ ≡-sym e₁)
        ≡⟨ ≡-cong (≡-sym e₁ ◂_) (◂-▸-comm e₁ (F₁ y f) (≡-sym e₁)) ⟩
          ≡-sym e₁ ◂ ((e₁ ◂ F₁ y f) ▸ ≡-sym e₁)
        ≈⟨ ◂-resp-≈ (≡-sym e₁) (▸-resp-≈ (x≃y .F₁≡) (≡-sym e₁)) ⟨
          ≡-sym e₁ ◂ (F₁ x f ▸ e₁ ▸ ≡-sym e₁)
        ≡⟨ ≡-cong (≡-sym e₁ ◂_) (▸-assocʳ (F₁ x f) (≡-sym e₁)) ⟩
          ≡-sym e₁ ◂ (F₁ x f ▸ ≡-trans e₁ (≡-sym e₁))
        ≡⟨ ≡-cong (λ p → ≡-sym e₁ ◂ (F₁ x f ▸ p)) (Rel₂.trans-symʳ e₁) ⟩
          ≡-sym e₁ ◂ F₁ x f
        ∎
      } where e₁ = F₀≡ x≃y

    ≃-trans : Transitive {A = Morphism 𝒬 𝒬′} _≃_
    ≃-trans {i} {j} {k} i≃j j≃k = record
      { F₀≡ = ≡-trans (F₀≡ i≃j) (F₀≡ j≃k)
      ; F₁≡ = λ {_ _ f} → begin
        F₁ i f ▸ ≡-trans (F₀≡ i≃j) (F₀≡ j≃k) ≡⟨ ▸-assocʳ (F₁ i f) (F₀≡ j≃k) ⟨
        (F₁ i f ▸ F₀≡ i≃j) ▸ F₀≡ j≃k         ≈⟨ ▸-resp-≈ (F₁≡ i≃j) (F₀≡ j≃k) ⟩
        (F₀≡ i≃j ◂ F₁ j f) ▸ F₀≡ j≃k         ≡⟨ ◂-▸-comm (F₀≡ i≃j) (F₁ j f) (F₀≡ j≃k) ⟨
        F₀≡ i≃j ◂ (F₁ j f ▸ F₀≡ j≃k)         ≈⟨ ◂-resp-≈ (F₀≡ i≃j) (F₁≡ j≃k) ⟩
        F₀≡ i≃j ◂ (F₀≡ j≃k ◂ F₁ k f)         ≡⟨ ◂-assocˡ (F₀≡ i≃j) (F₁ k f) ⟩
        ≡-trans (F₀≡ i≃j) (F₀≡ j≃k) ◂ F₁ k f ∎
      }

  ≃-isEquivalence : Rel₂.IsEquivalence _≃_
  ≃-isEquivalence = record
    { refl  = ≃-refl
    ; sym   = ≃-sym
    ; trans = ≃-trans
    }

module _
  {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″}
  ⦃ eq : Equivalence C e′ ⦄
  where

  infix 5 _∣ˡ_
  _∣ˡ_ : Morphism B C → Morphism A C → Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  G ∣ˡ F = Σ[ J ∈ Morphism A B ] G ∘ J ≃ F

id-isHomomorphism : {𝒬 : Quiver o ℓ} → ⦃ eq : Equivalence 𝒬 e′ ⦄ → IsHomomorphism eq eq id
id-isHomomorphism = record { F-resp-≈ = Function.id }

id-isFunctor :
  {𝒬 : Quiver o ℓ} → (C : Category.Signature 𝒬) →
  ⦃ eq : Equivalence 𝒬 e′ ⦄ →
  IsFunctor eq eq C C id
id-isFunctor _ = record
  { F-resp-id = refl
  ; F-resp-∘ = refl
  }

id-isCartesian :
  (𝒞 : Category.t o ℓ e) (let module 𝒞 = Category.t 𝒞)
  (C : Cartesian.t 𝒞.category) →
  IsCartesian 𝒞.eq 𝒞.eq C C id
id-isCartesian 𝒞 C = record
  { ⊤-iso = record
    { from = 𝒞.id ; to = 𝒞.id
    ; isIso = record { isoˡ = 𝒞.identityˡ ; isoʳ = 𝒞.identityʳ }
    }
  ; ×-iso = λ A B → record
    { from = 𝒞.id ; to = 𝒞.id
    ; isIso = record { isoˡ = 𝒞.identityˡ ; isoʳ = 𝒞.identityʳ }
    }
  ; F-resp-! = 𝒞.identityˡ
  ; F-resp-π₁ = 𝒞.identityʳ
  ; F-resp-π₂ = 𝒞.identityʳ
  ; F-resp-⟨⟩ = λ _ _ → 𝒞.identityˡ
  } where module 𝒞 = Category.t 𝒞

module _
  {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″}
  ⦃ eqᵃ : Equivalence A e ⦄ ⦃ eqᵇ : Equivalence B e′ ⦄ ⦃ eqᶜ : Equivalence C e″ ⦄
  where

  ∘-isHomomorphism :
    {G : Morphism B C} {F : Morphism A B} →
    IsHomomorphism eqᵇ eqᶜ G → IsHomomorphism eqᵃ eqᵇ F →
    IsHomomorphism eqᵃ eqᶜ (G ∘ F)
  ∘-isHomomorphism isG isF .IsHomomorphism.F-resp-≈ = G.resp-≈ ⊙ F.resp-≈
    where module F = IsHomomorphism isF
          module G = IsHomomorphism isG

module _
  {A B C : Quiver o ℓ}
  ⦃ eqᵇ : Equivalence B e′ ⦄ ⦃ eqᶜ : Equivalence C e″ ⦄
  where

  open _≃_
  open EdgeReasoning
  open Transport (C .Hom)
  open TransportOverQ (C .Hom) (eqᶜ ._≈_)
  open Transport (B .Hom) using () renaming (_▸_ to _▹_; _◂_ to _◃_)
  open TransportMor (B .Hom) (C .Hom)

  ≃-resp-∘ :
    {f g : Morphism B C} {h i : Morphism A B} →
    (is : IsHomomorphism eqᵇ eqᶜ g) →
    f ≃ g → h ≃ i → f ∘ h ≃ g ∘ i
  ≃-resp-∘ {f} {g} {h} {i} isHomo f≃g h≃i = record
    { F₀≡ = ≡-trans (≡-cong (F₀ f) (F₀≡ h≃i)) (F₀≡ f≃g)
    ; F₁≡ = λ {_ _ j} → begin
        F₁ (f ∘ h) j ▸ ≡-trans (≡-cong (F₀ f) (F₀≡ h≃i)) (F₀≡ f≃g)
      ≡⟨ ▸-assocʳ (F₁ f (F₁ h j)) e₁ ⟨
        F₁ f (F₁ h j) ▸ ≡-cong (F₀ f) e₂ ▸ e₁
      ≡⟨ ≡-cong (_▸ e₁) (M-resp-▸ (F₀ f) (F₁ f) (F₁ h j) e₂) ⟨
        F₁ f (F₁ h j ▹ e₂) ▸ e₁
      ≈⟨ F₁≡ f≃g ⟩
        e₁ ◂ F₁ g (F₁ h j ▹ e₂)
      ≈⟨ ◂-resp-≈ e₁ (IsHomomorphism.F-resp-≈ isHomo (F₁≡ h≃i)) ⟩
        e₁ ◂ F₁ g (e₂ ◃ F₁ i j)
      ≡⟨ ≡-cong (e₁ ◂_) (M-resp-◂ (F₀ g) (F₁ g) e₂ (F₁ i j)) ⟩
        e₁ ◂ ≡-cong (F₀ g) e₂ ◂ F₁ g (F₁ i j)
      ≡⟨ ◂-assocˡ e₁ (F₁ g (F₁ i j)) ⟩
        ≡-trans e₁ (≡-cong (F₀ g) e₂) ◂ F₁ g (F₁ i j)
      ≡⟨ ≡-cong (_◂ F₁ g (F₁ i j)) (Rel₂.naturality λ _ → e₁) ⟨
        ≡-trans (≡-cong (F₀ f) (F₀≡ h≃i)) (F₀≡ f≃g) ◂ F₁ (g ∘ i) j
      ∎
    } where
      e₁ = F₀≡ f≃g
      e₂ = F₀≡ h≃i

