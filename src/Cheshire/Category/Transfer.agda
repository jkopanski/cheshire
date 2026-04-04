{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Category.Transfer where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Category.Bundle as Bundle
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)

open import Cheshire.Category.Structure using (IsCategory)
open Category using (_[_∘_])

private
  variable
    o o′ ℓ ℓ′ e : 𝕃.t

module _
  {𝒮 : Quiver o′ ℓ′} {S : Category.t 𝒮}
  {𝒯 : Quiver o ℓ}   {T : Category.t 𝒯} ⦃ eqₜ : Equivalence 𝒯 e ⦄
  (is : IsCategory eqₜ T)
  (F : Morphism.Functor′ eqₜ S T)
  where

  private
    module F = Morphism.Functor′ F
    module S = Category.t S
    module T where
      open Category.t T public
      open IsCategory is public
      open HomReasoning public

  open T

  structure : IsCategory F.eqₛ S
  structure = record
    { assoc = λ {f = f} {g} {h} → begin
        F.₁ (S [ S [ h ∘ g ] ∘ f ]) ≈⟨ F.resp-∘ ⟩
        F.₁ (S [ h ∘ g ]) ∘ F.₁ f   ≈⟨ ∘-resp-≈ˡ F.resp-∘ ⟩
        (F.₁ h ∘ F.₁ g) ∘ F.₁ f     ≈⟨ assoc ⟩
        F.₁ h ∘ F.₁ g ∘ F.₁ f       ≈⟨ ∘-resp-≈ʳ F.resp-∘ ⟨
        F.₁ h ∘ F.₁ (S [ g ∘ f ])   ≈⟨ F.resp-∘ ⟨
        F.₁ (S [ h ∘ S [ g ∘ f ] ]) ∎
    ; identityˡ = λ {f = f} → begin
        F.₁ (S [ S.id ∘ f ]) ≈⟨ F.resp-∘ ⟩
        F.₁ S.id ∘ F.₁ f     ≈⟨ ∘-resp-≈ˡ F.resp-id ⟩
        id ∘ F.₁ f           ≈⟨ identityˡ ⟩
        F.₁ f                ∎
    ; identityʳ = λ {f = f} → begin
        F.₁ (S [ f ∘ S.id ]) ≈⟨ F.resp-∘ ⟩
        F.₁ f ∘ F.₁ S.id     ≈⟨ ∘-resp-≈ʳ F.resp-id ⟩
        F.₁ f ∘ id           ≈⟨ identityʳ ⟩
        F.₁ f                ∎
    ; ∘-resp-≈ = λ {f = f} {h} {g} {i} f≈h g≈i → begin
        F.₁ (S [ f ∘ g ]) ≈⟨ F.resp-∘ ⟩
        F.₁ f ∘ F.₁ g     ≈⟨ ∘-resp-≈ f≈h g≈i ⟩
        F.₁ h ∘ F.₁ i     ≈⟨ F.resp-∘ ⟨
        F.₁ (S [ h ∘ i ]) ∎
    }

module _
  {𝒮 : Quiver o′ ℓ′} {S : Category.t 𝒮}
  (T : Bundle.Category o ℓ e) (let module T = Bundle.Category T)
  (F : Morphism.Functor′ T.eq S T.category)
  where

  bundle : Bundle.Category o′ ℓ′ e
  bundle = record
    { 𝒬 = 𝒮
    ; category = S
    ; isCategory = structure T.isCategory F
    }

