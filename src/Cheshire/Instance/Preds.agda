{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Instance.Preds where

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Object.Signatures as Object

open Rel₁ using (Pred; _∩_; _⟨→⟩_; _⟨×⟩_; IUniversal)

private
  variable
    a : 𝕃.t

𝒬 : ∀ o → (A : Set o) → Quiver (𝕃.suc o) o
𝒬 o A = mk⇒ {Ob = Pred A o} λ A B → ∀[ A Rel₁.⇒ B ]

module _ {o : 𝕃.t} {A : Set o} where

  instance
    eq : Equivalence (𝒬 o A) o
    eq = record
      { _≈_ = λ {P} f g → (x : A) → (y : P x) → f y ≡ g y
      ; equiv = record
        { refl  = λ _ _ → ≡-refl
        ; sym   = λ α a x → ≡-sym (α a x)
        ; trans = λ α β a x → ≡-trans (α a x) (β a x)
        }
      }

  category : Category.Signature (𝒬 o A)
  category = record
    { id = Function.id
    ; _∘_ = λ α β → α ⊙ β
    }

  open Object (𝒬 o A .Ob)

  instance
    terminal : Terminal
    terminal = record { ⊤ = Rel₁.U }

    products : BinaryProducts
    products = record { _×_ = _∩_ }

  cartesian : Cartesian.Signature category
  cartesian = record
    { terminal = terminal
    ; ! = λ _ → 𝟙.tt
    ; products = products
    ; π₁ = λ x → x .proj₁
    ; π₂ = λ x → x .proj₂
    ; ⟨_,_⟩ = λ f g x → f x , g x
    }
