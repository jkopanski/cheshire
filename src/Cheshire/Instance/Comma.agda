{-# OPTIONS --allow-unsolved-metas #-}

module Cheshire.Instance.Comma where

open import Cheshire.Core
open import Cheshire.Signatures
open import Cheshire.Homomorphism.Signatures
open import Cheshire.Homomorphism.Structures
open import Cheshire.Homomorphism.Bundles using (Functor)
import Cheshire.Bundles as Bundles
import Cheshire.Structures as Structures

open Category renaming (_∘_ to _[_∘_])

module _
  {o ℓ o′ ℓ′ o″ ℓ″ : 𝕃.t}
  {𝒜 : Quiver o  ℓ }
  {ℬ : Quiver o′ ℓ′}
  {𝒞 : Quiver o″ ℓ″}
  {e e′ e″} ⦃ eq : Equivalence 𝒜 e ⦄ ⦃ eq′ : Equivalence ℬ e′ ⦄ ⦃ eq″ : Equivalence 𝒞 e″ ⦄
  {A : Bundles.Category 𝒜}  {B : Bundles.Category ℬ} {C : Bundles.Category 𝒞}
  where

  module A = Bundles.Category A
  module B = Bundles.Category B

  open Bundles.Category C
  open Reasoning

  record ↓Ob (S : Morphism 𝒜 𝒞) (T : Morphism ℬ 𝒞) : Set (o ⊔ o′ ⊔ ℓ″) where
    no-eta-equality
    private
      module S = Morphism S
      module T = Morphism T
    field
      {α} : 𝒜 .Ob
      {β} : ℬ .Ob
      f : 𝒞 .Hom (S.₀ α) (T.₀ β)

  open ↓Ob

  record ↓Hom {S : Morphism 𝒜 𝒞} {T : Morphism ℬ 𝒞} (A B : ↓Ob S T) : Set (ℓ ⊔ ℓ′ ⊔ e″) where
    no-eta-equality
    private
      module S = Morphism S
      module T = Morphism T

    field
      g : 𝒜 .Hom (A .α) (B .α)
      h : ℬ .Hom (A .β) (B .β)
      -- S.₀ (A .α) --- A .f --> T.₀ (A .β)
      --     |                       |
      --   S.₁ g                   T.₁ h
      --     |                       |
      --     V                       V
      -- S.₀ (B .α) --- B .f --> T.₀ (B .β)
      commute : CommutativeSquare (A .f) (S.₁ g) (T.₁ h) (B .f)

  𝒬 : Morphism 𝒜 𝒞 → Morphism ℬ 𝒞 → Quiver (o ⊔ o′ ⊔ ℓ″) (ℓ ⊔ ℓ′ ⊔ e″)
  𝒬 S T = mk⇒ {Ob = ↓Ob S T} ↓Hom

  Comma :
    {S : Morphism 𝒜 𝒞} {T : Morphism ℬ 𝒞} →
    (F : IsFunctor S A.signature signature) (G : IsFunctor T B.signature signature) → Category (𝒬 S T)
  Comma {S} {T} F G = record
    { id = ↓id
    ; _∘_ = ↓∘
    } where
      module S where
        open Morphism S public
        open IsFunctor F public
      module T where
        open Morphism T public
        open IsFunctor G public
      open ↓Hom

      ↓id : ∀ {E : ↓Ob S T} → ↓Hom E E
      ↓id {E} = record
        { g = A.id
        ; h = B.id
        ; commute = begin
            T.₁ B.id ∘ E .f ≈⟨ elimˡ T.F-resp-id ⟩
            E .f ≈⟨ introʳ S.F-resp-id ⟩
            E .f ∘ S.₁ A.id ∎
        }

      ↓∘ : ∀ {X Y Z : ↓Ob S T} → ↓Hom Y Z → ↓Hom X Y → ↓Hom X Z
      ↓∘ {X} {Y} {Z} a₁ a₂ = record
        { g = A.signature [ a₁ .g ∘ a₂ .g ]
        ; h = B.signature [ a₁ .h ∘ a₂ .h ]
        ; commute = begin
          T.₁ (a₁ .h B.∘ a₂ .h) ∘ X .f       ≈⟨ T.F-resp-∘ ⟩∘⟨refl ⟩
          (T.₁ (a₁ .h) ∘ T.₁ (a₂ .h)) ∘ X .f ≈⟨ glue (a₁ .commute) (a₂ .commute) ⟩
          Z .f ∘ (S.₁ (a₁ .g) ∘ S.₁ (a₂ .g)) ≈˘⟨ refl⟩∘⟨ S.F-resp-∘ ⟩
          Z .f ∘ (S.₁ (a₁ .g A.∘ a₂ .g))     ∎
        }
