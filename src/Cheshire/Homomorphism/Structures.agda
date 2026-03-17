{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Homomorphism.Signatures hiding (_∘_)

module Cheshire.Homomorphism.Structures where

import Data.Product as ×
import Relation.Binary.Construct.On as On

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Cartesian.Signature as Cartesian renaming (Cartesian to t)
import Cheshire.Object.Signatures as Object
import Cheshire.Morphism as Morphisms

open Object
private
  variable
    o ℓ o′ ℓ′ : 𝕃.t
    𝒮 𝒯 : Quiver o ℓ

module _ {e} (eqₛ : Equivalence 𝒯 e) (ℳ : Morphism 𝒮 𝒯) where
  private
    module M = Morphism ℳ

  equivalence : Equivalence 𝒮 e
  equivalence = record
    { _≈_ = _≈_ on M.₁
    ; equiv = On.isEquivalence M.₁ equiv
    } where instance _ = eqₛ

module _
  {e e′}
  ⦃ eqₛ : Equivalence 𝒮 e ⦄
  ⦃ eqₜ : Equivalence 𝒯 e′ ⦄
  where

  record IsHomomorphism (ℳ : Morphism 𝒮 𝒯) : Set (𝕃.levelOfTerm ℳ ⊔ e ⊔ e′) where
    private
      open Quiver 𝒮
      module M = Morphism ℳ

    field
      F-resp-≈ : ∀ {A B} {f g : A ⇒ B} → f ≈ g → M.₁ f ≈ M.₁ g

    -- for nicer module use: F.resp-≈
    resp-≈ = F-resp-≈


  record IsFunctor
    (S : Category.t 𝒮) (T : Category.t 𝒯)
    (ℳ : Morphism 𝒮 𝒯) :
    Set (𝕃.levelOfTerm ℳ ⊔ e′) where
    private
      open Quiver 𝒮
      module M = Morphism ℳ
      module S = Category.t S
      module T = Category.t T
      open T using (_∘_)

    field
      F-resp-id : ∀ {A} → M.₁ (S.id {A}) ≈ T.id
      F-resp-∘ : ∀ {X Y Z} → {f : X ⇒ Y} {g : Y ⇒ Z} →
                 M.₁ (g S.∘ f) ≈ M.₁ g ∘ M.₁ f

    resp-id = F-resp-id
    resp-∘  = F-resp-∘


  record IsCartesian
    {𝒮′ : Category.t 𝒮} {𝒯′ : Category.t 𝒯}
    (S : Cartesian.t 𝒮′) (T : Cartesian.t 𝒯′)
    (ℳ : Morphism 𝒮 𝒯) :
    Set (𝕃.levelOfTerm ℳ ⊔ e′) where
    private
      module M = Morphism ℳ
      module S = Cartesian.t S
      module T = Cartesian.t T
      open Category.t 𝒯′ using (_∘_)
      open Morphisms.Bundles 𝒯′

    private instance
      _ = S.terminal; _ = T.terminal
      _ = S.products; _ = T.products

    field
      -- This is actually something different in agda-categories.  It's
      -- a lawful ⊤ and × moved to the target category.
      -- F-resp-⊤ : ⊤ ≅ F₀ ⊤
      -- F-resp-× : ∀ {A B} → F₀ A × F₀ B ≅ F₀ (A × B)

      ⊤-iso : ⊤ ≅ M.₀ ⊤
      ×-iso : ∀ (A B : 𝒮 .Ob) → M.₀ A × M.₀ B ≅ M.₀ (A × B )

    module ⊤-iso = _≅_ ⊤-iso
    module ×-iso {A B} = _≅_ (×-iso A B)

    field
      F-resp-! :
        ∀ {A} →
        ⊤-iso.to ∘ M.₁ (S.! {A}) ≈ T.!
      F-resp-⟨⟩ :
        ∀ {A B X} →
        (f : 𝒮 [ X , A ]) → (g : 𝒮 [ X , B ]) →
        ×-iso.to ∘ M.₁ S.⟨ f , g ⟩ ≈ T.⟨ M.₁ f , M.₁ g ⟩
      F-resp-π₁ :
        ∀ {A B} →
        M.₁ (S.π₁ {A} {B}) ∘ ×-iso.from ≈ T.π₁
      F-resp-π₂ :
        ∀ {A B} →
        M.₁ (S.π₂ {A} {B}) ∘ ×-iso.from ≈ T.π₂
