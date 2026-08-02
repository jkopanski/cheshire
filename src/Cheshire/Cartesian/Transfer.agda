{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Cartesian.Transfer where

import Cheshire.Category.Signature as Category renaming (Category to t)
import Cheshire.Category.Bundle as Bundle
import Cheshire.Category.Transfer as Transfer
import Cheshire.Cartesian.Signature as Cartesian renaming (Cartesian to t)
import Cheshire.Cartesian.Bundle as Bundle
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Morphism.Reasoning as MorphismReasoning

open import Cheshire.Category.Structure using (IsCategory)
open import Cheshire.Cartesian.Structure using (IsCartesian)

open Category using (_[_∘_])

private
  variable
    o o′ ℓ ℓ′ e : 𝕃.t

module _
  {𝒮 : Quiver o′ ℓ′} {S′ : Category.t 𝒮} {S : Cartesian.t S′}
  {𝒯 : Quiver o ℓ}   {T′ : Category.t 𝒯} {T : Cartesian.t T′}
  ⦃ eqₜ : Equivalence 𝒯 e ⦄
  {T-is : IsCategory eqₜ T′} (T-isCartesian : IsCartesian T-is T)
  {F : Morphism.t 𝒮 𝒯}
  (let eqₛ = Morphism.equivalence eqₜ F)
  (isF : Morphism.IsFunctor eqₛ eqₜ S′ T′ F)
  (isC : Morphism.IsCartesian eqₛ eqₜ S T F)
  where

  private
    module F where
      open Morphism.t F public
      open Morphism.IsFunctor isF public
      open Morphism.IsCartesian isC public
    module S where
      is-category : IsCategory eqₛ S′
      is-category = Transfer.structure T-is isF

      open Category.t S′ public
      open Cartesian.t S public
      open IsCategory is-category public

    module T where
      open Category.t T′ public
      open Cartesian.t T public
      open IsCartesian T-isCartesian public
      open IsCategory T-is public
      open HomReasoning public
      open MorphismReasoning T-is public

  open T

  structure : IsCartesian S.is-category S
  structure = record
    { !-unique = λ f → begin
        F.₁ S.!                             ≈⟨ introˡ F.⊤-iso.isoʳ ○ assoc ⟩
        F.⊤-iso.from ∘ F.⊤-iso.to ∘ F.₁ S.! ≈⟨ refl⟩∘⟨ F.resp-! ⟩
        F.⊤-iso.from ∘ T.!                  ≈⟨ refl⟩∘⟨ T.!-unique (F.⊤-iso.to T.∘ F.₁ f) ⟩
        F.⊤-iso.from ∘ F.⊤-iso.to ∘ F.₁ f   ≈⟨ cancelˡ F.⊤-iso.isoʳ ⟩
        F.₁ f                               ∎
    ; project₁ = λ {h = h} {i} → begin
        F.₁ (S′ [ S.π₁ ∘ S.⟨ h , i ⟩ ])                            ≈⟨ F.resp-∘ ⟩
        F.₁ S.π₁ ∘ F.₁ S.⟨ h , i ⟩                                 ≈⟨ intro-center F.×-iso.isoʳ ○ assoc²δγ ⟩
        (F.₁ S.π₁ ∘ F.×-iso.from) ∘ (F.×-iso.to ∘ F.₁ S.⟨ h , i ⟩) ≈⟨ F.resp-π₁ ⟩∘⟨ F.resp-⟨⟩ h i ⟩
        π₁ ∘ T.⟨ F.₁ h , F.₁ i ⟩                                   ≈⟨ project₁ ⟩
        F.₁ h                                                      ∎
    ; project₂ = λ {h = h} {i} → begin
        F.₁ (S′ [ S.π₂ ∘ S.⟨ h , i ⟩ ])                            ≈⟨ F.resp-∘ ⟩
        F.₁ S.π₂ ∘ F.₁ S.⟨ h , i ⟩                                 ≈⟨ intro-center F.×-iso.isoʳ ○ assoc²δγ ⟩
        (F.₁ S.π₂ ∘ F.×-iso.from) ∘ (F.×-iso.to ∘ F.₁ S.⟨ h , i ⟩) ≈⟨ F.resp-π₂ ⟩∘⟨ F.resp-⟨⟩ h i ⟩
        π₂ ∘ T.⟨ F.₁ h , F.₁ i ⟩                                   ≈⟨ project₂ ⟩
        F.₁ i                ∎
    ; unique = λ {h = h} {i} {j} π₁∘h≈i π₂∘h≈q →
      begin
        F.₁ S.⟨ i , j ⟩
      ≈⟨ introˡ F.×-iso.isoʳ ○ assoc ⟩
        F.×-iso.from ∘ F.×-iso.to ∘ F.₁ S.⟨ i , j ⟩
      ≈⟨ refl⟩∘⟨ F.resp-⟨⟩ i j ⟩
        F.×-iso.from ∘ ⟨ F.₁ i , F.₁ j ⟩
      ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟺ π₁∘h≈i ○ F.resp-∘) (⟺ π₂∘h≈q ○ F.resp-∘) ⟩
        F.×-iso.from ∘ ⟨ F.₁ S.π₁ ∘ F.₁ h , F.₁ S.π₂ ∘ F.₁ h ⟩
      ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟨
        F.×-iso.from ∘ ⟨ F.₁ S.π₁ , F.₁ S.π₂ ⟩ ∘ F.₁ h
      ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (introʳ F.×-iso.isoʳ) (introʳ F.×-iso.isoʳ) ⟩∘⟨refl ⟩
        F.×-iso.from ∘ ⟨ F.₁ S.π₁ ∘ F.×-iso.from ∘ F.×-iso.to , F.₁ S.π₂ ∘ F.×-iso.from ∘ F.×-iso.to ⟩ ∘ F.₁ h
      ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (pullˡ F.resp-π₁) (pullˡ F.resp-π₂) ⟩∘⟨refl ⟩
        F.×-iso.from ∘ ⟨ π₁ ∘ F.×-iso.to , π₂ ∘ F.×-iso.to ⟩ ∘ F.₁ h
      ≈⟨ refl⟩∘⟨ (⟺ ⟨⟩∘ ⟩∘⟨refl ○ assoc) ⟩
        F.×-iso.from ∘ ⟨ π₁ , π₂ ⟩ ∘ F.×-iso.to ∘ F.₁ h
      ≈⟨ refl⟩∘⟨ elimˡ η ⟩
        F.×-iso.from ∘ F.×-iso.to ∘ F.₁ h
      ≈⟨ cancelˡ F.×-iso.isoʳ ⟩
        F.₁ h
      ∎
    }

module _
  {𝒮 : Quiver o′ ℓ′} {S′ : Category.t 𝒮} {S : Cartesian.t S′}
  (T : Bundle.Cartesian o ℓ e) (let module T = Bundle.Cartesian T)
  {F : Morphism.t 𝒮 T.𝒬}
  (let eqₛ = Morphism.equivalence T.eq F)
  (isF : Morphism.IsFunctor eqₛ T.eq S′ T.category F)
  (isC : Morphism.IsCartesian eqₛ T.eq S T.cartesian F)
  where

  C : Bundle.Category o′ ℓ′ e
  C = Transfer.bundle
    record { Bundle.Cartesian T }
    isF

  bundle : Bundle.Cartesian o′ ℓ′ e
  bundle = record
    { Bundle.Category C
    ; cartesian = S
    ; isCartesian = structure T.isCartesian isF isC
    }
