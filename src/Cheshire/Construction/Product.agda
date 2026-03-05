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
import Cheshire.Category.Signature as Signatures
import Cheshire.Category.Structure as IsCategory renaming (IsCategory to t)
import Cheshire.Structures as Structures
import Cheshire.Bundles as Bundles
import Cheshire.Homomorphism as Homo

open × using (_×_; _,_; <_,_>; proj₁; proj₂)

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

  module _
    {o″ ℓ″}
    (C₁ : Quiver o ℓ) (C₂ : Quiver o′ ℓ′) (C₃ : Quiver o″ ℓ″)
    where

    assocˡ : Homo.Morphism (𝒬 (𝒬 C₁ C₂) C₃) (𝒬 C₁ (𝒬 C₂ C₃))
    assocˡ = record
      { F₀ = < proj₁ ⊙ proj₁ , < proj₂ ⊙ proj₁ , proj₂ > >
      ; F₁ = < proj₁ ⊙ proj₁ , < proj₂ ⊙ proj₁ , proj₂ > >
      }

    assocʳ : Homo.Morphism (𝒬 C₁ (𝒬 C₂ C₃)) (𝒬 (𝒬 C₁ C₂) C₃)
    assocʳ = record
      { F₀ = < < proj₁ , proj₁ ⊙ proj₂ > , proj₂ ⊙ proj₂ >
      ; F₁ = < < proj₁ , proj₁ ⊙ proj₂ > , proj₂ ⊙ proj₂ >
      }

  πˡ : (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) → Homo.Morphism (𝒬 𝒮 𝒯) 𝒮
  πˡ _ _ = record
    { F₀ = proj₁
    ; F₁ = proj₁
    }

  πʳ : (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) →  Homo.Morphism (𝒬 𝒮 𝒯) 𝒯
  πʳ _ _ = record
    { F₀ = proj₂
    ; F₁ = proj₂
    }

  Swap : (𝒮 : Quiver o ℓ) (𝒯 : Quiver o′ ℓ′) →  Homo.Morphism (𝒬 𝒮 𝒯) (𝒬 𝒯 𝒮)
  Swap _ _ = record
    { F₀ = ×.swap
    ; F₁ = ×.swap
    }

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
    (isS : IsCategory.t e S) (isT : IsCategory.t e′ T) →
    IsCategory.t (e ⊔ e′) (Signature.Category S T)
  IsCategory S T = record
    { eq = equivalence S.eq T.eq
    ; assoc = S.assoc , T.assoc
    ; identityˡ = S.identityˡ , T.identityˡ
    ; identityʳ = S.identityʳ , T.identityʳ
    ; ∘-resp-≈ = ×.zip S.∘-resp-≈ T.∘-resp-≈
    } where module S = IsCategory.t S
            module T = IsCategory.t T

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

  module _
    {o″ ℓ″ e e′ e″}
    {C₁ : Quiver o ℓ} {C₂ : Quiver o′ ℓ′} {C₃ : Quiver o″ ℓ″}
    (eq₁ : Equivalence C₁ e) (eq₂ : Equivalence C₂ e′) (eq₃ : Equivalence C₃ e″)
    where

    module eq₁ = Equivalence eq₁
    module eq₂ = Equivalence eq₂
    module eq₃ = Equivalence eq₃

    assocˡ-isHomomorphism :
      Homo.IsHomomorphism
        (Signature.assocˡ C₁ C₂ C₃)
        (equivalence (equivalence eq₁ eq₂) eq₃)
        (equivalence eq₁ (equivalence eq₂ eq₃))
    assocˡ-isHomomorphism = record
      { F-resp-≈ = < proj₁ ⊙ proj₁ , < proj₂ ⊙ proj₁ , proj₂ > > }

    assocˡ-isFunctor :
      (C₁′ : Signatures.Category C₁) (C₂′ : Signatures.Category C₂) (C₃′ : Signatures.Category C₃) →
      Homo.IsFunctor
        (Signature.assocˡ C₁ C₂ C₃)
        (equivalence (equivalence eq₁ eq₂) eq₃)
        (equivalence eq₁ (equivalence eq₂ eq₃))
        (Signature.Category (Signature.Category C₁′ C₂′) C₃′)
        (Signature.Category C₁′ (Signature.Category C₂′ C₃′))
    assocˡ-isFunctor _ _ _ = record
      { Homo.IsHomomorphism assocˡ-isHomomorphism
      ; F-resp-id = eq₁.refl , (eq₂.refl , eq₃.refl)
      ; F-resp-∘ = eq₁.refl , (eq₂.refl , eq₃.refl)
      }

    assocʳ-isHomomorphism :
      Homo.IsHomomorphism
        (Signature.assocʳ C₁ C₂ C₃)
        (equivalence eq₁ (equivalence eq₂ eq₃))
        (equivalence (equivalence eq₁ eq₂) eq₃)
    assocʳ-isHomomorphism = record
      { F-resp-≈ = < < proj₁ , proj₁ ⊙ proj₂ > , proj₂ ⊙ proj₂ > }

    assocʳ-isFunctor :
      (C₁′ : Signatures.Category C₁) (C₂′ : Signatures.Category C₂) (C₃′ : Signatures.Category C₃) →
      Homo.IsFunctor
        (Signature.assocʳ C₁ C₂ C₃)
        (equivalence eq₁ (equivalence eq₂ eq₃))
        (equivalence (equivalence eq₁ eq₂) eq₃)
        (Signature.Category C₁′ (Signature.Category C₂′ C₃′))
        (Signature.Category (Signature.Category C₁′ C₂′) C₃′)
    assocʳ-isFunctor _ _ _ = record
      { Homo.IsHomomorphism assocʳ-isHomomorphism
      ; F-resp-id = (eq₁.refl , eq₂.refl) , eq₃.refl
      ; F-resp-∘ = (eq₁.refl , eq₂.refl) , eq₃.refl
      }

  module _
    {e e′ : 𝕃.t}
    (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′)
    where

    module eqₛ = Equivalence eqₛ
    module eqₜ = Equivalence eqₜ

    πˡ-isHomomorphism :
      Homo.IsHomomorphism (Signature.πˡ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₛ
    πˡ-isHomomorphism = record
      { F-resp-≈ = proj₁ }

    πˡ-isFunctor :
      (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) →
      Homo.IsFunctor (Signature.πˡ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₛ (Signature.Category S T) S
    πˡ-isFunctor _ _ = record
      { Homo.IsHomomorphism πˡ-isHomomorphism
      ; F-resp-id = eqₛ.refl
      ; F-resp-∘ = eqₛ.refl
      }

    πʳ-isHomomorphism :
      Homo.IsHomomorphism (Signature.πʳ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₜ
    πʳ-isHomomorphism = record
      { F-resp-≈ = proj₂ }

    πʳ-isFunctor :
      (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) →
      Homo.IsFunctor (Signature.πʳ 𝒮 𝒯) (equivalence eqₛ eqₜ) eqₜ (Signature.Category S T) T
    πʳ-isFunctor _ _ = record
      { Homo.IsHomomorphism πʳ-isHomomorphism
      ; F-resp-id = eqₜ.refl
      ; F-resp-∘ = eqₜ.refl
      }

    Swap-isHomomorphism :
      Homo.IsHomomorphism (Signature.Swap 𝒮 𝒯) (equivalence eqₛ eqₜ) (equivalence eqₜ eqₛ)
    Swap-isHomomorphism = record
      { F-resp-≈ = ×.swap }

    Swap-isFunctor :
      (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) →
      Homo.IsFunctor
        (Signature.Swap 𝒮 𝒯)
        (equivalence eqₛ eqₜ) (equivalence eqₜ eqₛ)
        (Signature.Category S T) (Signature.Category T S)
    Swap-isFunctor _ _ = record
      { Homo.IsHomomorphism Swap-isHomomorphism
      ; F-resp-id = eqₜ.refl , eqₛ.refl
      ; F-resp-∘ = eqₜ.refl , eqₛ.refl
      }

module Bundle where

  open Homo using (Homomorphism; Functor)
  open Signature using (_※_; _⁂_)

  Category :
    {e e′ : 𝕃.t} →
    (S : Bundles.Category e 𝒮) (T : Bundles.Category e′ 𝒯) →
    Bundles.Category (e ⊔ e′) (𝒬 𝒮 𝒯)
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

  module _
    {o″ ℓ″ e e′ e″}
    {C₁ : Quiver o ℓ} {C₂ : Quiver o′ ℓ′} {C₃ : Quiver o″ ℓ″}
    (eq₁ : Equivalence C₁ e) (eq₂ : Equivalence C₂ e′) (eq₃ : Equivalence C₃ e″)
    where

    assocˡ-Homomorphism :
      Homomorphism
        (Structure.equivalence (Structure.equivalence eq₁ eq₂) eq₃)
        (Structure.equivalence eq₁ (Structure.equivalence eq₂ eq₃))
    assocˡ-Homomorphism = record
      { signature = Signature.assocˡ C₁ C₂ C₃
      ; structure = Structure.assocˡ-isHomomorphism eq₁ eq₂ eq₃
      }

    assocˡ-Functor :
      (C₁′ : Signatures.Category C₁) (C₂′ : Signatures.Category C₂) (C₃′ : Signatures.Category C₃) →
      Functor
        (Structure.equivalence (Structure.equivalence eq₁ eq₂) eq₃)
        (Structure.equivalence eq₁ (Structure.equivalence eq₂ eq₃))
        (Signature.Category (Signature.Category C₁′ C₂′) C₃′)
        (Signature.Category C₁′ (Signature.Category C₂′ C₃′))
    assocˡ-Functor C₁′ C₂′ C₃′ = record
      { signature = Signature.assocˡ C₁ C₂ C₃
      ; structure = Structure.assocˡ-isFunctor eq₁ eq₂ eq₃ C₁′ C₂′ C₃′
      }

    assocʳ-Homomorphism :
      Homomorphism
        (Structure.equivalence eq₁ (Structure.equivalence eq₂ eq₃))
        (Structure.equivalence (Structure.equivalence eq₁ eq₂) eq₃)
    assocʳ-Homomorphism = record
      { signature = Signature.assocʳ C₁ C₂ C₃
      ; structure = Structure.assocʳ-isHomomorphism eq₁ eq₂ eq₃
      }

    assocʳ-Functor :
      (C₁′ : Signatures.Category C₁) (C₂′ : Signatures.Category C₂) (C₃′ : Signatures.Category C₃) →
      Functor
        (Structure.equivalence eq₁ (Structure.equivalence eq₂ eq₃))
        (Structure.equivalence (Structure.equivalence eq₁ eq₂) eq₃)
        (Signature.Category C₁′ (Signature.Category C₂′ C₃′))
        (Signature.Category (Signature.Category C₁′ C₂′) C₃′)
    assocʳ-Functor C₁′ C₂′ C₃′ = record
      { signature = Signature.assocʳ C₁ C₂ C₃
      ; structure = Structure.assocʳ-isFunctor eq₁ eq₂ eq₃ C₁′ C₂′ C₃′
      }

  module _
    {e e′ : 𝕃.t}
    (eqₛ : Equivalence 𝒮 e) (eqₜ : Equivalence 𝒯 e′)
    where

    module eqₛ = Equivalence eqₛ
    module eqₜ = Equivalence eqₜ

    πˡ-Homomorphism :
      Homomorphism (Structure.equivalence eqₛ eqₜ) eqₛ
    πˡ-Homomorphism = record
      { signature = Signature.πˡ 𝒮 𝒯
      ; structure = Structure.πˡ-isHomomorphism eqₛ eqₜ
      }

    πˡ-Functor :
      (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) →
      Functor (Structure.equivalence eqₛ eqₜ) eqₛ (Signature.Category S T) S
    πˡ-Functor S T = record
      { signature = Signature.πˡ 𝒮 𝒯
      ; structure = Structure.πˡ-isFunctor eqₛ eqₜ S T
      }

    πʳ-Homomorphism :
      Homomorphism (Structure.equivalence eqₛ eqₜ) eqₜ
    πʳ-Homomorphism = record
      { signature = Signature.πʳ 𝒮 𝒯
      ; structure = Structure.πʳ-isHomomorphism eqₛ eqₜ
      }

    πʳ-Functor :
      (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) →
      Functor (Structure.equivalence eqₛ eqₜ) eqₜ (Signature.Category S T) T
    πʳ-Functor S T = record
      { signature = Signature.πʳ 𝒮 𝒯
      ; structure = Structure.πʳ-isFunctor eqₛ eqₜ S T
      }

    Swap-Homomorphism :
      Homomorphism (Structure.equivalence eqₛ eqₜ) (Structure.equivalence eqₜ eqₛ)
    Swap-Homomorphism = record
      { signature = Signature.Swap 𝒮 𝒯
      ; structure = Structure.Swap-isHomomorphism eqₛ eqₜ
      }

    Swap-Functor :
      (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) →
      Functor (Structure.equivalence eqₛ eqₜ) (Structure.equivalence eqₜ eqₛ) (Signature.Category S T) (Signature.Category T S)
    Swap-Functor S T = record
      { signature = Signature.Swap 𝒮 𝒯
      ; structure = Structure.Swap-isFunctor eqₛ eqₜ S T
      }
