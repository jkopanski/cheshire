{-# OPTIONS --safe #-}

module Cheshire.Core where

import Overture
open import Overture
  hiding (module Func; module ×; _⊎_)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans) public
import Algebra

open 𝕃 using (_⊔_) public
open Algebra using (Op₁; Op₂)

module Func where
  open Overture using (module Func)
  open Func public

  module _ {c ℓ} (S : Setoid.t c ℓ) where
    open Setoid.t S renaming (Carrier to X; _≈_ to eq)

    unary : {f : Op₁ X} → Algebra.Congruent₁ eq f → S ⟶ₛ S
    unary {f} _ .Func.t.to = f
    unary cong .Func.t.cong = cong

  module _ {c ℓ} (S : Setoid.t c ℓ) where
    open Setoid.t S renaming (Carrier to X; _≈_ to eq; isEquivalence to isEq)

    binary : {f : Op₂ X} → Algebra.Congruent₂ eq f → S ⟶ₛ (S ⇨ S)
    binary {f} eq .Func.t.to = λ x → record
      { to = λ y → f x y
      ; cong = eq (Rel₂.IsEquivalence.refl isEq)
      }
    binary eq .Func.t.cong = λ x≈y _ → eq x≈y (Rel₂.IsEquivalence.refl isEq)

  module _ {c ℓ} (m : Algebra.Magma c ℓ) where
    open Algebra.Magma m renaming (setoid to S)

    magma : S ⟶ₛ (S ⇨ S)
    magma = binary S ∙-cong

open Func using (_⟨$⟩_; _⟶ₛ_; _⇨_) public

open Function
  using (case_of_; case_returning_of_; const; flip; _on_; _$_)
  renaming (_∘_ to _⊙_) public

record Quiver o ℓ : Set (𝕃.suc (o 𝕃.⊔ ℓ)) where
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

record Equivalence (𝒬 : Quiver o ℓ) (e : 𝕃.t) : Set (o 𝕃.⊔ ℓ 𝕃.⊔ 𝕃.suc e) where
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

