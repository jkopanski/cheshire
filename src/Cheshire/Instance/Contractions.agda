{-# OPTIONS --safe --guardedness #-}

open import Cheshire.Core

module Cheshire.Instance.Contractions (o : 𝕃.t) where

import Codata.Guarded.Stream as Stream renaming (Stream to t)
import Codata.Guarded.Stream.Properties as Streamₚ

import Cheshire.Category as Category renaming (Category to t)
import Cheshire.Cartesian as Cartesian renaming (Cartesian to t)
import Cheshire.Homomorphism as Morphism renaming (Morphism to t)
import Cheshire.Prop as Prop
import Cheshire.Construction.Sub.Morphism as Sub

import Cheshire.Instance.Streams o as Streams renaming (Streams to t)

open ℕ using (_<_; _≤_; _+_; _⊓_)
open Stream using (_[_])

𝒮 = Streams.𝒬
module S = Cartesian.t Streams.t

private
  variable
    A B C : Set o
    d e m n : ℕ.t
    s t : Stream.t A
    f g h : 𝒮 .Hom A B

infix 4 _≡[_]_
_≡[_]_ : ∀ {a} {A : Set a} → Stream.t A → ℕ.t → Stream.t A → Set _
s ≡[ n ] t = ∀ i → i < n → (s [ i ]) ≡ (t [ i ])

≡[≤] : m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] m≤n s≈ₙt i i<m = s≈ₙt i (ℕ.≤-trans i<m m≤n)

≡[+] : s ≡[ m + n ] t → s ≡[ m ] t
≡[+] s≈t = ≡[≤] (ℕ.m≤m+n _ _) s≈t

infix 4 _↓_
_↓_ : 𝒮 .Hom A B → ℕ.t → Set _
f ↓ d = ∀ {n s t} → s ≡[ n ] t → f ⟨$⟩ s ≡[ d + n ] f ⟨$⟩ t

≡-↓ : d ≡ e → f ↓ d → f ↓ e
≡-↓ ≡-refl = Function.id

≤-↓ : e ≤ d → f ↓ d → f ↓ e
≤-↓ d≤e f↓d {n} s~t = ≡[≤] (ℕ.+-monoˡ-≤ n d≤e) (f↓d s~t)

map↓ : ∀ (f : A → B) → Streams.map f ↓ 0
map↓ f {_} {s} {t} s~t i i<n = begin
  Stream.map f s [ i ] ≡⟨ Streamₚ.lookup-map i f s ⟩
  f (s [ i ])          ≡⟨ ≡-cong f (s~t i i<n) ⟩
  f (t [ i ])          ≡⟨ Streamₚ.lookup-map i f t ⟨
  Stream.map f t [ i ] ∎
  where open Rel₂.≡-Reasoning

R : Rel₁.Pred (𝒮 .Hom A  B) o
R f = ∃[ δ ] f ↓ δ

𝒬 : Quiver (𝕃.suc o) o
𝒬 = Sub.𝒬 Streams.𝒬 R

H : Morphism.t 𝒬 Streams.𝒬
H = Sub.H Streams.𝒬 R

private module H = Morphism.t H

categoryᴾ : Prop.Category R S.category
categoryᴾ = record
  { id = 0 , Function.id
  ; _∘_ = λ where
    (e , g↓) (d , f↓) →
      ( e + d
      , λ s~t i i<e+d+n → g↓ (f↓ s~t) i (ℕ.≤-trans i<e+d+n (ℕ.≤-reflexive (ℕ.+-assoc e d _)))
      -- rewrite ℕ.+-assoc e d n = g↓ ⊙ f↓
      )
  }

⟨⟩↓ : ∀ {f : 𝒮 .Hom C A} {g : 𝒮 .Hom C B} → f ↓ d → g ↓ e → S.⟨ f , g ⟩ ↓ (d ⊓ e)
⟨⟩↓ {d = d} {e} {f = f} {g} f↓ g↓ {s = s} {t} s~t i i<d⊓e+n =
  begin
    S.⟨ f , g ⟩ ⟨$⟩ s [ i ]
  ≡⟨⟩
    Stream.lookup (Stream.zipWith _,_ (f ⟨$⟩ s) (g ⟨$⟩ s)) i
  ≡⟨ Streamₚ.lookup-zipWith i _,_ (f ⟨$⟩ s) (g ⟨$⟩ s) ⟩
    (f ⟨$⟩ s [ i ]) , (g ⟨$⟩ s [ i ])
  ≡⟨ Rel₂.cong₂ _,_
      (≤-↓ {f = f} (ℕ.m⊓n≤m d e) f↓ s~t i i<d⊓e+n)
      (≤-↓ {f = g} (ℕ.m⊓n≤n d e) g↓ s~t i i<d⊓e+n) ⟩
    (f ⟨$⟩ t [ i ]) , (g ⟨$⟩ t [ i ])
  ≡⟨ Streamₚ.lookup-zipWith i _,_ (f ⟨$⟩ t) (g ⟨$⟩ t) ⟨
    S.⟨ f , g ⟩ ⟨$⟩ t [ i ]
  ∎ where open Rel₂.≡-Reasoning

cartesianᴾ : Prop.Cartesian R S.cartesian
cartesianᴾ = record
  { ! = 0 , λ _ _ _ → ≡-refl
  ; π₁ = 0 , map↓ proj₁
  ; π₂ = 0 , map↓ proj₂
  ; ⟨_,_⟩ = λ where
    {f = f} {g} (d , f↓) (e , g↓) → d ⊓ e , ⟨⟩↓ {f = f} {g} f↓ g↓
  }

Contractions : Cartesian.t (𝕃.suc o) (o ⊔ o) o
Contractions = Sub.Bundles.cartesian Streams.t R categoryᴾ cartesianᴾ
