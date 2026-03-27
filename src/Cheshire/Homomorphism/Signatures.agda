{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Homomorphism.Signatures where

import Cheshire.Object.Signatures as Object
import Cheshire.Morphism.Signatures as Morphisms

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : 𝕃.t

record Morphism (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  no-eta-equality
  constructor mkM
  open Quiver 𝒮
  open Quiver 𝒯 renaming (_⇒_ to _⇒ₜ_)

  field
    F₀ : 𝒮 .Ob → 𝒯 .Ob
    F₁ : ∀ {A B} → A ⇒ B → F₀ A ⇒ₜ F₀ B

  ₀ = F₀
  ₁ = F₁

open Morphism public

{-# DISPLAY ₀ F = F₀ F #-}
{-# DISPLAY ₁ F = F₁ F #-}

id : ∀ {A : Quiver o ℓ} → Morphism A A
id .F₀ = Function.id
id .F₁ = Function.id

infixr 9 _∘_
_∘_ :
  ∀ {A : Quiver o ℓ} {B : Quiver o′ ℓ′} {C : Quiver o″ ℓ″} →
  Morphism B C → Morphism A B → Morphism A C
_∘_ G F .F₀ = G .F₀ ⊙ F .F₀
_∘_ G F .F₁ = G .F₁ ⊙ F .F₁

module _ {𝒮 : Quiver o ℓ} {𝒯 : Quiver o′ ℓ′} (ℳ : Morphism 𝒮 𝒯) where

  private
    module M = Morphism ℳ
    open Quiver 𝒯
    open Morphisms 𝒯
    open Object using (⊤; ⊥; A×B; A+B; _×_; _⊎_)

  record Terminal
    ⦃ _ : Object.Terminal (𝒮 .Ob) ⦄ ⦃ _ : Object.Terminal (𝒯 .Ob) ⦄
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      ⊤-iso : ⊤ ⇔ M.₀ ⊤

    module ⊤-iso = _⇔_ ⊤-iso

    -- additional Felix names
    ε : ⊤ ⇒ M.₀ ⊤
    ε = ⊤-iso.from

    ε⁻¹ : M.₀ ⊤ ⇒ ⊤
    ε⁻¹ = ⊤-iso.to


  record Initial
    ⦃ _ : Object.Initial (𝒮 .Ob) ⦄ ⦃ _ : Object.Initial (𝒯 .Ob) ⦄
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      ⊥-iso : ⊥ ⇔ M.₀ ⊥

    module ⊥-iso = _⇔_ ⊥-iso


  record Product
    (A B : 𝒮 .Ob)
    ⦃ _ : Object.Product (𝒮 .Ob) A B ⦄ ⦃ _ : Object.Product (𝒯 .Ob) (M.₀ A) (M.₀ B) ⦄
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      A×B-iso : A×B ⇔ M.₀ A×B

    module A×B-iso = _⇔_ A×B-iso


  record Coproduct
    (A B : 𝒮 .Ob)
    ⦃ _ : Object.Coproduct (𝒮 .Ob) A B ⦄ ⦃ _ : Object.Coproduct (𝒯 .Ob) (M.₀ A) (M.₀ B) ⦄
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      A+B-iso : A+B ⇔ M.₀ A+B

    module A+B-iso = _⇔_ A+B-iso


  record BinaryProducts
    ⦃ _ : Object.BinaryProducts (𝒮 .Ob) ⦄ ⦃ _ : Object.BinaryProducts (𝒯 .Ob) ⦄
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      ×-iso : ∀ (A B : 𝒮 .Ob) → M.₀ A × M.₀ B ⇔ M.₀ (A × B )

    module ×-iso {A B} = _⇔_ (×-iso A B)

    -- additional Felix names
    μ : ∀ {A B} → M.₀ A × M.₀ B ⇒ M.₀ (A × B)
    μ = ×-iso.from

    μ⁻¹ : ∀ {A B} → M.₀ (A × B) ⇒ M.₀ A × M.₀ B
    μ⁻¹ = ×-iso.to


  record BinaryCoproducts
    ⦃ _ : Object.BinaryCoproducts (𝒮 .Ob) ⦄ ⦃ _ : Object.BinaryCoproducts (𝒯 .Ob) ⦄
      : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
    no-eta-equality
    field
      ⊎-iso : ∀ (A B : 𝒮 .Ob) → M.₀ A ⊎ M.₀ B ⇔ M.₀ (A ⊎ B )

    module ⊎-iso {A B} = _⇔_ (⊎-iso A B)
