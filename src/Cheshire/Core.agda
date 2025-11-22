{-# OPTIONS --safe #-}

module Cheshire.Core where

import Algebra

open Algebra using (Op₁; Op₂)

module 𝕃 where
  open import Level renaming (Level to t) public

open 𝕃 using (_⊔_) public

module 𝟘 where
  import Data.Empty as 𝟘0ℓ
  open import Data.Empty.Polymorphic renaming (⊥ to t) public

module 𝟙 where
  import Data.Unit as 𝟙0ℓ
  open import Data.Unit.Polymorphic renaming (⊤ to t; tt to tt-lift) public
  pattern tt = 𝕃.lift 𝟙0ℓ.tt

module Rel₀ where
  open import Relation.Nullary public

module Rel₁ where
  open import Relation.Unary hiding (∅; U) public
  open import Relation.Unary.Polymorphic public

module Rel₂ where
  open import Relation.Binary public hiding (Setoid)
  open import Relation.Binary.PropositionalEquality public

open Rel₂ using (Rel) public

module Setoid where
  open import Relation.Binary.Bundles using () renaming (Setoid to t) public
  import Relation.Binary.Reasoning.Setoid as SetoidR
  module Reasoning {s₁ s₂} (S : t s₁ s₂) = SetoidR S

  lift : ∀ {c ℓ} (o r : 𝕃.t) → t c ℓ → t (o 𝕃.⊔ c) (r 𝕃.⊔ ℓ)
  lift o r S = record
    { Carrier = 𝕃.Lift o Carrier
    ; _≈_ = λ where
      (𝕃.lift x) (𝕃.lift y) → 𝕃.Lift r (x ≈ y)
    ; isEquivalence = record
      { refl = 𝕃.lift (Rel₂.IsEquivalence.refl (t.isEquivalence S))
      ; sym = λ where
        (𝕃.lift eq) → 𝕃.lift (Rel₂.IsEquivalence.sym (t.isEquivalence S) eq)
      ; trans = λ where
        (𝕃.lift eq) (𝕃.lift eq′) → 𝕃.lift (Rel₂.IsEquivalence.trans (t.isEquivalence S) eq eq′)
      }
    } where open t S

module Func where
  open import Function.Bundles renaming (Func to t) public
  open import Function.Relation.Binary.Setoid.Equality public

  module _ {c ℓ} (S : Setoid.t c ℓ) where
    open Setoid.t S renaming (Carrier to X; _≈_ to eq)

    unary : {f : Op₁ X} → Algebra.Congruent₁ eq f → S ⟶ₛ S
    unary {f} _ .t.to = f
    unary cong .t.cong = cong

  module _ {c ℓ} (S : Setoid.t c ℓ) where
    open Setoid.t S renaming (Carrier to X; _≈_ to eq; isEquivalence to isEq)

    binary : {f : Op₂ X} → Algebra.Congruent₂ eq f → S ⟶ₛ (S ⇨ S)
    binary {f} eq .t.to = λ x → record
      { to = λ y → f x y
      ; cong = eq (Rel₂.IsEquivalence.refl isEq)
      }
    binary eq .t.cong = λ x≈y _ → eq x≈y (Rel₂.IsEquivalence.refl isEq)

  module _ {c ℓ} (m : Algebra.Magma c ℓ) where
    open Algebra.Magma m renaming (setoid to S)

    magma : S ⟶ₛ (S ⇨ S)
    magma = binary S ∙-cong

open Func using (_⟨$⟩_; _⟶ₛ_; _⇨_) public

module Function where
  open import Function renaming (_∘_ to _⊙_) public

open Function using (case_of_; case_returning_of_; const; flip; _on_; _$_) public

record Quiver o ℓ : Set (𝕃.suc (o ⊔ ℓ)) where
  no-eta-equality
  constructor mk⇒
  infix 4 _⇒_
  field
    {Ob} : Set o
    Hom : Rel Ob ℓ

  _⇒_ : Rel Ob ℓ
  _⇒_ = Hom

open Quiver using (Ob; Hom) public

private
  variable
    o ℓ : 𝕃.t

_[_,_] : (𝒬 : Quiver o ℓ) → Rel (𝒬 .Ob) ℓ
𝒬 [ a , b ] = 𝒬 .Hom a b

{-# DISPLAY Hom 𝒬 A B = 𝒬 [ A , B ] #-}
{-# DISPLAY Quiver._⇒_ 𝒬 A B = 𝒬 [ A , B ] #-}

record Equivalence (𝒬 : Quiver o ℓ) (e : 𝕃.t) : Set (o ⊔ ℓ ⊔ 𝕃.suc e) where
  infix  4 _≈_
  open Quiver 𝒬 using (_⇒_)
  field
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e
    equiv : ∀ {A B} → Rel₂.IsEquivalence (_≈_ {A} {B})

  setoid : {A B : 𝒬 .Ob} → Setoid.t ℓ e
  setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  module Equiv {A B : 𝒬 .Ob} = Rel₂.IsEquivalence (equiv {A} {B})
  module EdgeReasoning {A B : 𝒬 .Ob} = Setoid.Reasoning (setoid {A} {B})

  open Equiv public

open Equivalence ⦃ … ⦄ public

{-# DISPLAY Equivalence._≈_ _ f g = f ≈ g #-}

_[_≈_] :
  ∀ {𝒬 : Quiver o ℓ} {e} {A B : 𝒬 .Ob } →
  (eq : Equivalence 𝒬 e) → (f g : 𝒬 .Hom A B) → Set e
_[_≈_] eq = Equivalence._≈_ eq

