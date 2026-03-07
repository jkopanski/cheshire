{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Bifunctor.Structure where

import Cheshire.Category as Category renaming (Category to t)
open import Cheshire.Bifunctor.Signature

open Category using (_[_∘_]; IsCategory)

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ : 𝕃.t
    e e′ e″ : 𝕃.t

module _
  {𝒞 : Quiver o ℓ} {𝒟 : Quiver o′ ℓ′} {ℰ : Quiver o″ ℓ″}
  {C : Category.Signature 𝒞} {D : Category.Signature 𝒟} {E : Category.Signature ℰ}
  (eqᶜ : Equivalence 𝒞 e) (eqᵈ : Equivalence 𝒟 e′) (eqᵉ : Equivalence ℰ e″)
  where

  record IsBifunctor (H : Bifunctor 𝒞 𝒟 ℰ)
    : Set (o ⊔ o′ ⊔ o″ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ e ⊔ e′ ⊔ e″) where
    module H = Bifunctor H
    module eqᶜ = Equivalence eqᶜ
    module eqᵈ = Equivalence eqᵈ
    module eqᵉ = Equivalence eqᵉ

    field
      resp-≈ˡ :
        ∀ {A B d} {f g : 𝒞 [ A , B ]} →
        eqᶜ [ f ≈ g ] →
        eqᵉ [ H.₁ˡ {d = d} f ≈ H.₁ˡ g ]
      resp-≈ʳ :
        ∀ {A B c} {f g : 𝒟 [ A , B ]} →
        eqᵈ [ f ≈ g ] →
        eqᵉ [ H.₁ʳ {c = c} f ≈ H.₁ʳ g ]

      resp-∘ˡ :
        ∀ {X Y Z d} {f : 𝒞 [ X , Y ]} {g : 𝒞 [ Y , Z ]} →
        eqᵉ [ H.₁ˡ {d = d} (C [ g ∘ f ]) ≈ E [ H.₁ˡ g ∘ H.₁ˡ f ] ]

      resp-∘ʳ :
        ∀ {X Y Z c} {f : 𝒟 [ X , Y ]} {g : 𝒟 [ Y , Z ]} →
        eqᵉ [ H.₁ʳ {c = c} (D [ g ∘ f ]) ≈ E [ H.₁ʳ g ∘ H.₁ʳ f ] ]

    homomorphismˡ = resp-∘ˡ
    homomorphismʳ = resp-∘ʳ
