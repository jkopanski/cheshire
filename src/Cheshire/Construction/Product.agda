{-# OPTIONS --safe #-}

-- I have no idea why agda-categories doesn't put this under
-- Construction hierarchy.  I do since I'll need this in the
-- Cheshire.Signatures for the Monoidal.  Also this could construct
-- other structures than Category, like Cartesian, given the inputs
-- have the same structure.  I don't know yet how to untangle those
-- module dependencies.  I might not need it anyway.

open import Cheshire.Core

module Cheshire.Construction.Product where

import Data.Product as ×
import Cheshire.Signatures.Core as Signatures
import Cheshire.Structures as Structures
import Cheshire.Bundles as Bundles
import Cheshire.Homomorphism as Homo

open × using (_×_; _,_; <_,_>)

private
  variable
    o o′ ℓ ℓ′ : 𝕃.t

𝒬 : (𝒮 : Quiver o ℓ) (T : Quiver o′ ℓ′) → Quiver (o ⊔ o′) (ℓ ⊔ ℓ′)
𝒬 𝒮 𝒯 = record
  { Ob = 𝒮 .Ob × 𝒯 .Ob
  ; Hom = ×.zipWith (𝒮 .Hom) (𝒯 .Hom) _×_
  }

private
  variable
    𝒮 𝒯 : Quiver o ℓ
    𝒮₁ 𝒯₁ : Quiver o ℓ
    𝒮₂ 𝒯₂ : Quiver o ℓ

module Signature where

  Category : (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) → Signatures.Category (𝒬 𝒮 𝒯)
  Category S T = record
    { id = S.id , T.id
    ; _∘_ = ×.zip S._∘_ T._∘_
    } where module S = Signatures.Category S
            module T = Signatures.Category T

  infixr 2 _※_
  _※_ : (F : Homo.Morphism 𝒮 𝒯₁) → (G : Homo.Morphism 𝒮 𝒯₂) → Homo.Morphism 𝒮 (𝒬 𝒯₁ 𝒯₂)
  F ※ G = record
    { F₀ = < F.₀ , G.₀ >
    ; F₁ = < F.₁ , G.₁ >
    } where module F = Homo.Morphism F
            module G = Homo.Morphism G

  infixr 2 _⁂_
  _⁂_ : (F : Homo.Morphism 𝒮₁ 𝒯₁) → (G : Homo.Morphism 𝒮₂ 𝒯₂) → Homo.Morphism (𝒬 𝒮₁ 𝒮₂) (𝒬 𝒯₁ 𝒯₂)
  F ⁂ G = record
    { F₀ = ×.map F.₀ G.₀
    ; F₁ = ×.map F.₁ G.₁
    } where module F = Homo.Morphism F
            module G = Homo.Morphism G

module Structure where

  open Signature using (_※_; _⁂_)

  equivalence : ∀ {e e′} → Equivalence 𝒮 e → Equivalence 𝒯 e′ → Equivalence (𝒬 𝒮 𝒯) (e ⊔ e′)
  equivalence S T = record
    { _≈_ = ×.zipWith S._≈_ T._≈_ _×_
    ; equiv = record
      { refl = S.refl , T.refl
      ; sym = ×.map S.sym T.sym
      ; trans = ×.zip S.trans T.trans
      }
    } where module S = Equivalence S
            module T = Equivalence T

  IsCategory :
    {e e′ : 𝕃.t} →
    {S : Signatures.Category 𝒮} {T : Signatures.Category 𝒯} →
    (isS : Structures.IsCategory e S) (isT : Structures.IsCategory e′ T) →
    Structures.IsCategory (e ⊔ e′) (Signature.Category S T)
  IsCategory S T = record
    { eq = equivalence S.eq T.eq
    ; assoc = S.assoc , T.assoc
    ; identityˡ = S.identityˡ , T.identityˡ
    ; identityʳ = S.identityʳ , T.identityʳ
    ; ∘-resp-≈ = ×.zip S.∘-resp-≈ T.∘-resp-≈
    } where module S = Structures.IsCategory S
            module T = Structures.IsCategory T

  module _
    {e e′ e″ : 𝕃.t}
    {eqₛ : Equivalence 𝒮 e} {eqₜ₁ : Equivalence 𝒯₁ e′} {eqₜ₂ : Equivalence 𝒯₂ e″}
    {F : Homo.Morphism 𝒮 𝒯₁} {G : Homo.Morphism 𝒮 𝒯₂}
    where

    ※-isHomomorphism :
      (isF : Homo.IsHomomorphism F eqₛ eqₜ₁) → (isG : Homo.IsHomomorphism G eqₛ eqₜ₂) →
      Homo.IsHomomorphism (F ※ G) eqₛ (equivalence eqₜ₁ eqₜ₂)
    ※-isHomomorphism isF isG = record
      { F-resp-≈ = < F.resp-≈ , G.resp-≈ >
      } where module F = Homo.IsHomomorphism isF
              module G = Homo.IsHomomorphism isG

    ※-isFunctor :
      {S : Signatures.Category 𝒮} {T₁ : Signatures.Category 𝒯₁} {T₂ : Signatures.Category 𝒯₂} →
      (isF : Homo.IsFunctor F eqₛ eqₜ₁ S T₁) → (isG : Homo.IsFunctor G eqₛ eqₜ₂ S T₂) →
      Homo.IsFunctor (F ※ G) eqₛ (equivalence eqₜ₁ eqₜ₂) S (Signature.Category T₁ T₂)
    ※-isFunctor isF isG = record
      { Homo.IsHomomorphism isHomomorphism
      ; F-resp-id = F.resp-id , G.resp-id
      ; F-resp-∘ = F.resp-∘ , G.resp-∘
      } where module F = Homo.IsFunctor isF
              module G = Homo.IsFunctor isG
              isHomomorphism = ※-isHomomorphism F.isHomomorphism G.isHomomorphism

  module _
    {e e′ e″ e‴ : 𝕃.t}
    {eqₛ₁ : Equivalence 𝒮₁ e} {eqₛ₂ : Equivalence 𝒮₂ e′} {eqₜ₁ : Equivalence 𝒯₁ e″} {eqₜ₂ : Equivalence 𝒯₂ e‴}
    {F : Homo.Morphism 𝒮₁ 𝒯₁} {G : Homo.Morphism 𝒮₂ 𝒯₂}
    where

    ⁂-isHomomorphism :
      (isF : Homo.IsHomomorphism F eqₛ₁ eqₜ₁) → (isG : Homo.IsHomomorphism G eqₛ₂ eqₜ₂) →
      Homo.IsHomomorphism (F ⁂ G) (equivalence eqₛ₁ eqₛ₂) (equivalence eqₜ₁ eqₜ₂)
    ⁂-isHomomorphism isF isG = record
      { F-resp-≈ = ×.map F.resp-≈ G.resp-≈
      } where module F = Homo.IsHomomorphism isF
              module G = Homo.IsHomomorphism isG

    ⁂-isFunctor :
      {S₁ : Signatures.Category 𝒮₁} {S₂ : Signatures.Category 𝒮₂} {T₁ : Signatures.Category 𝒯₁} {T₂ : Signatures.Category 𝒯₂} →
      (isF : Homo.IsFunctor F eqₛ₁ eqₜ₁ S₁ T₁) → (isG : Homo.IsFunctor G eqₛ₂ eqₜ₂ S₂ T₂) →
      Homo.IsFunctor (F ⁂ G) (equivalence eqₛ₁ eqₛ₂) (equivalence eqₜ₁ eqₜ₂) (Signature.Category S₁ S₂) (Signature.Category T₁ T₂)
    ⁂-isFunctor isF isG = record
      { Homo.IsHomomorphism isHomomorphism
      ; F-resp-id = F.resp-id , G.resp-id
      ; F-resp-∘ = F.resp-∘ , G.resp-∘
      } where module F = Homo.IsFunctor isF
              module G = Homo.IsFunctor isG
              isHomomorphism = ⁂-isHomomorphism F.isHomomorphism G.isHomomorphism

module Bundle where

  open Homo using (Homomorphism; Functor)
  open Signature using (_※_; _⁂_)

  Category :
    {e e′ : 𝕃.t} →
    (S : Bundles.Category 𝒮 e) (T : Bundles.Category 𝒯 e′) →
    Bundles.Category (𝒬 𝒮 𝒯) (e ⊔ e′)
  Category S T = record
    { signature = Signature.Category S.signature T.signature
    ; structure = Structure.IsCategory S.structure T.structure
    } where module S = Bundles.Category S
            module T = Bundles.Category T

  module _
    {e e′ e″ : 𝕃.t}
    {eqₛ : Equivalence 𝒮 e} {eqₜ₁ : Equivalence 𝒯₁ e′} {eqₜ₂ : Equivalence 𝒯₂ e″}
    where

    ※-Homomorphism :
      (F : Homomorphism eqₛ eqₜ₁) (G : Homomorphism eqₛ eqₜ₂) →
      Homomorphism eqₛ (Structure.equivalence eqₜ₁ eqₜ₂)
    ※-Homomorphism F G = record
      { signature = F.signature ※ G.signature
      ; structure = Structure.※-isHomomorphism F.structure G.structure
      } where module F = Homo.Homomorphism F
              module G = Homo.Homomorphism G

    ※-Functor :
      {S : Signatures.Category 𝒮} {T₁ : Signatures.Category 𝒯₁} {T₂ : Signatures.Category 𝒯₂} →
      (F : Functor eqₛ eqₜ₁ S T₁) (G : Functor eqₛ eqₜ₂ S T₂) →
      Functor eqₛ (Structure.equivalence eqₜ₁ eqₜ₂) S (Signature.Category T₁ T₂)
    ※-Functor F G = record
      { signature = F.signature ※ G.signature
      ; structure = Structure.※-isFunctor F.structure G.structure
      } where module F = Functor F
              module G = Functor G

  module _
    {e e′ e″ e‴ : 𝕃.t}
    {eqₛ₁ : Equivalence 𝒮₁ e} {eqₛ₂ : Equivalence 𝒮₂ e′} {eqₜ₁ : Equivalence 𝒯₁ e″} {eqₜ₂ : Equivalence 𝒯₂ e‴}
    where

    ⁂-Homomorphism :
      (F : Homomorphism eqₛ₁ eqₜ₁) (G : Homomorphism eqₛ₂ eqₜ₂) →
      Homomorphism (Structure.equivalence eqₛ₁ eqₛ₂) (Structure.equivalence eqₜ₁ eqₜ₂)
    ⁂-Homomorphism F G = record
      { signature = F.signature ⁂ G.signature
      ; structure = Structure.⁂-isHomomorphism F.structure G.structure
      } where module F = Homo.Homomorphism F
              module G = Homo.Homomorphism G

    ⁂-Functor :
      {S₁ : Signatures.Category 𝒮₁} {S₂ : Signatures.Category 𝒮₂} {T₁ : Signatures.Category 𝒯₁} {T₂ : Signatures.Category 𝒯₂} →
      (F : Functor eqₛ₁ eqₜ₁ S₁ T₁) (G : Functor eqₛ₂ eqₜ₂ S₂ T₂) →
      Functor
        (Structure.equivalence eqₛ₁ eqₛ₂) (Structure.equivalence eqₜ₁ eqₜ₂)
        (Signature.Category S₁ S₂) (Signature.Category T₁ T₂)
    ⁂-Functor F G = record
      { signature = F.signature ⁂ G.signature
      ; structure = Structure.⁂-isFunctor F.structure G.structure
      } where module F = Functor F
              module G = Functor G
