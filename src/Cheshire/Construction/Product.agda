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

open × using (_×_; _,_)

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

module Signature where

  Category : (S : Signatures.Category 𝒮) (T : Signatures.Category 𝒯) → Signatures.Category (𝒬 𝒮 𝒯)
  Category S T = record
    { id = S.id , T.id
    ; _∘_ = ×.zip S._∘_ T._∘_
    } where module S = Signatures.Category S
            module T = Signatures.Category T

module Structure where

  IsCategory :
    {e e′ : 𝕃.t} →
    {S : Signatures.Category 𝒮} {T : Signatures.Category 𝒯} →
    (isS : Structures.IsCategory e S) (isT : Structures.IsCategory e′ T) →
    Structures.IsCategory (e ⊔ e′) (Signature.Category S T)
  IsCategory {𝒮 = 𝒮} {𝒯 = 𝒯} {e} {e′} S T = record
    { eq = eq
    ; assoc = S.assoc , T.assoc
    ; identityˡ = S.identityˡ , T.identityˡ
    ; identityʳ = S.identityʳ , T.identityʳ
    ; ∘-resp-≈ = ×.zip S.∘-resp-≈ T.∘-resp-≈
    } where module S = Structures.IsCategory S
            module T = Structures.IsCategory T
            eq : Equivalence (𝒬 𝒮 𝒯) (e ⊔ e′)
            eq = record
              { _≈_ = ×.zipWith _≈_ _≈_ _×_
              ; equiv = record
                { refl = refl , refl
                ; sym = ×.map sym sym
                ; trans = ×.zip (trans ⦃ S.eq ⦄) (trans ⦃ T.eq ⦄)
                }
              }

module Bundle where

  Category :
    {e e′ : 𝕃.t} →
    (S : Bundles.Category 𝒮 e) (T : Bundles.Category 𝒯 e′) →
    Bundles.Category (𝒬 𝒮 𝒯) (e ⊔ e′)
  Category S T = record
    { signature = Signature.Category S.signature T.signature
    ; structure = Structure.IsCategory S.structure T.structure
    } where module S = Bundles.Category S
            module T = Bundles.Category T
