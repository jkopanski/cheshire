{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Object.Signatures

module Cheshire.Instance.Syntactic {o ℓ} (U : Quiver o ℓ) where

import Cheshire.Morphism.Signatures as Morphism
import Cheshire.Signatures as Sig
import Cheshire.Homomorphism.Signatures as Homo

open Homo.Morphism

module Category where

  infix 4 _`⇒_
  data _`⇒_ : Rel (U .Ob) (o ⊔ ℓ) where
    ■_ : ∀ {A B : U .Ob} → U .Hom A B → A `⇒ B
    -- category
    `id : ∀ {A} → A `⇒ A
    _`∘_ : ∀ {A B C} → B `⇒ C → A `⇒ B → A `⇒ C

  𝒬 : Quiver o (o ⊔ ℓ)
  𝒬 = mk⇒ _`⇒_

  extend : Homo.Morphism U 𝒬
  extend = λ where
    .F₀ → Function.id
    .F₁ → ■_

  syntactic : Sig.Category 𝒬
  syntactic = λ where
    .id → `id
    ._∘_ → _`∘_
      where open Sig.Category

  module Synthesis
    {o′ ℓ′} {𝒯 : Quiver o′ ℓ′} (T : Sig.Category 𝒯)
    (H : Homo.Morphism U 𝒯)
    where

    module T = Sig.Category T
    module H = Homo.Morphism H

    open Sig.Category T

    H⁺ : Homo.Morphism 𝒬 𝒯
    H⁺ = Homo.mkM H.₀ F₁⁺
      where
        F₁⁺ : ∀ {A B} → 𝒬 .Hom A B → 𝒯 .Hom (H.₀ A) (H.₀ B)
        F₁⁺ (■ x) = H.₁ x
        F₁⁺ `id = id
        F₁⁺ (g `∘ f) = F₁⁺ g ∘ F₁⁺ f

    open Homo.Morphism H⁺ public

module Cartesian
  ⦃ _ : Terminal (U .Ob) ⦄
  ⦃ _ : BinaryProducts (U .Ob) ⦄
  where

  infix 4 _`⇒_
  data _`⇒_ : Rel (U .Ob) (o ⊔ ℓ) where
    ■_ : ∀ {A B : U .Ob} → U .Hom A B → A `⇒ B
    -- category
    `id : ∀ {A} → A `⇒ A
    _`∘_ : ∀ {A B C} → B `⇒ C → A `⇒ B → A `⇒ C
    -- terminal
    `! : ∀ {A} → A `⇒ ⊤
    -- product
    `π₁    : ∀ {A B} → A × B `⇒ A
    `π₂    : ∀ {A B} → A × B `⇒ B
    `⟨_,_⟩ : ∀ {A B C} → C `⇒ A → C `⇒ B → C `⇒ A × B

  𝒬 : Quiver o (o ⊔ ℓ)
  𝒬 = mk⇒ _`⇒_

  extend : Homo.Morphism U 𝒬
  extend = λ where
    .F₀ → Function.id
    .F₁ → ■_

  syntactic : Sig.Cartesian 𝒬
  syntactic = λ where
    .terminal → _
    .products → _
    .id    → `id
    ._∘_   → _`∘_
    .!     → `!
    .π₁    → `π₁
    .π₂    → `π₂
    .⟨_,_⟩ → `⟨_,_⟩
      where open Sig.Cartesian

  module _
    {o′ ℓ′} {𝒯 : Quiver o′ ℓ′} (T : Sig.Cartesian 𝒯)
    (H : Homo.Morphism U 𝒯)
    where

    module T = Sig.Cartesian T
    module H = Homo.Morphism H

    instance
      _ = T.terminal
      _ = T.products

    open Morphism 𝒯

    module Synthesis
      (ε : ⊤ ⇔ H .F₀ ⊤)
      (μ : ∀ (A B : 𝒬 .Ob) → H .F₀ A × H .F₀ B ⇔ H .F₀ (A × B))
      where

      open Sig.Cartesian T
      module ε = _⇔_ ε
      module μ {A B} = _⇔_ (μ A B)

      H⁺ : Homo.Morphism 𝒬 𝒯
      H⁺ = Homo.mkM H.₀ F₁⁺
        where
          F₁⁺ : ∀ {A B} → 𝒬 .Hom A B → 𝒯 .Hom (H.₀ A) (H.₀ B)
          F₁⁺ (■ x) = H.₁ x
          F₁⁺ `id = id
          F₁⁺ (g `∘ f) = F₁⁺ g ∘ F₁⁺ f
          F₁⁺ `! = ε.from ∘ !
          F₁⁺ `π₁ = π₁ ∘ μ.to
          F₁⁺ `π₂ = π₂ ∘ μ.to
          F₁⁺ `⟨ f , g ⟩ = μ.from ∘ ⟨ F₁⁺ f , F₁⁺ g ⟩

      open Homo.Morphism H⁺ public
