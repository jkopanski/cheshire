-- Copied with minor changes from agda-categories:
-- https://agda.github.io/agda-categories/Categories.Morphism.Reasoning.Core.html
-- which is licensed under the MIT license.
--   Copyright (c) 2019 Agda Github Community
{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Category.Signature
open import Cheshire.Category.Structure

module Cheshire.Morphism.Reasoning.Core
  {o ℓ} {𝒬 : Quiver o ℓ}
  {𝒞 : Category 𝒬 }
  {e : 𝕃.t} (isC : IsCategory e 𝒞)
  where

open Quiver 𝒬 using (_⇒_)
open Category 𝒞
open IsCategory isC
open HomReasoning
open Commutation

private
  variable
    A B C D : 𝒬 .Ob
    U V W X Y Z : 𝒬 .Ob
    f g h i : X ⇒ Y

module Identity where
  id-unique : ∀ {O} {f : O ⇒ O} → (∀ g → g ∘ f ≈ g) → f ≈ id
  id-unique g∘f≈g = trans (sym identityˡ) (g∘f≈g id)

  id-comm : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ id ∘ f
  id-comm = trans identityʳ (sym identityˡ)

  id-comm-sym : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f ∘ id
  id-comm-sym = trans identityˡ (sym identityʳ)

open Identity public

module Assoc4 where
  {-
  Explanation of naming scheme:

  Each successive association is given a Greek letter, from 'α' associated all
  the way to the left, to 'ε' associated all the way to the right. Then,
  'assoc²XY' is the proof that X is equal to Y. Explicitly:

  α = ((i ∘ h) ∘ g) ∘ f
  β = (i ∘ (h ∘ g)) ∘ f
  γ = (i ∘ h) ∘ (g ∘ f)
  δ = i ∘ ((h ∘ g) ∘ f)
  ε = i ∘ (h ∘ (g ∘ f))

  Only reassociations that need two assoc steps are defined here.
  -}

  assoc²αδ :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    ((i ∘ h) ∘ g) ∘ f ≈ i ∘ ((h ∘ g) ∘ f)
  assoc²αδ = ∘-resp-≈ˡ assoc ○ assoc

  assoc²αε :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    ((i ∘ h) ∘ g) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
  assoc²αε = assoc ○ assoc

  assoc²βγ :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    (i ∘ (h ∘ g)) ∘ f ≈ (i ∘ h) ∘ (g ∘ f)
  assoc²βγ = ∘-resp-≈ˡ (⟺ assoc) ○ assoc

  assoc²βε :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    (i ∘ (h ∘ g)) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
  assoc²βε = assoc ○ ∘-resp-≈ʳ assoc

  assoc²γβ :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    (i ∘ h) ∘ (g ∘ f) ≈ (i ∘ (h ∘ g)) ∘ f
  assoc²γβ = (⟺ assoc) ○ ∘-resp-≈ˡ assoc

  assoc²γδ :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    (i ∘ h) ∘ (g ∘ f) ≈ i ∘ ((h ∘ g) ∘ f)
  assoc²γδ = assoc ○ ∘-resp-≈ʳ (⟺ assoc)

  assoc²δα :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    i ∘ ((h ∘ g) ∘ f) ≈ ((i ∘ h) ∘ g) ∘ f
  assoc²δα = ⟺ assoc ○ ∘-resp-≈ˡ (⟺ assoc)

  assoc²δγ :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    i ∘ ((h ∘ g) ∘ f) ≈ (i ∘ h) ∘ (g ∘ f)
  assoc²δγ = ∘-resp-≈ʳ assoc ○ ⟺ assoc

  assoc²εα :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    i ∘ (h ∘ (g ∘ f)) ≈ ((i ∘ h) ∘ g) ∘ f
  assoc²εα = ⟺ assoc ○ ⟺ assoc

  assoc²εβ :
    ∀ {f : V ⇒ W} {g : W ⇒ X} {h : X ⇒ Y} {i : Y ⇒ Z} →
    i ∘ (h ∘ (g ∘ f)) ≈ (i ∘ (h ∘ g)) ∘ f
  assoc²εβ = ∘-resp-≈ʳ (⟺ assoc) ○ (⟺ assoc)

open Assoc4 public

-- Pulls use "a ∘ b ≈ c" as left-to-right rewrite
-- pull to the right / left of something existing
module Pulls {a : X ⇒ Y} {b : W ⇒ X} {c : W ⇒ Y} (ab≡c : a ∘ b ≈ c) where

  pullʳ :
    ∀ {f : Y ⇒ Z} →
    (f ∘ a) ∘ b ≈ f ∘ c
  pullʳ {f = f} = begin
    (f ∘ a) ∘ b ≈⟨ assoc ⟩
    f ∘ (a ∘ b) ≈⟨ refl⟩∘⟨ ab≡c ⟩
    f ∘ c       ∎

  pullˡ :
    ∀ {f : V ⇒ W} →
    a ∘ (b ∘ f) ≈ c ∘ f
  pullˡ {f = f} = begin
    a ∘ b ∘ f   ≈⟨ ⟺ assoc ⟩
    (a ∘ b) ∘ f ≈⟨ ab≡c ⟩∘⟨refl ⟩
    c ∘ f       ∎

open Pulls public

-- Pushes use "c ≈ a ∘ b" as a left-to-right rewrite
-- push to the right / left of something existing
module Pushes {a : X ⇒ Y} {b : W ⇒ X} {c : W ⇒ Y} (c≡ab : c ≈ a ∘ b) where
  pushʳ :
    ∀ {f : Y ⇒ Z} →
    f ∘ c ≈ (f ∘ a) ∘ b
  pushʳ {f = f} = begin
    f ∘ c       ≈⟨ refl⟩∘⟨ c≡ab ⟩
    f ∘ (a ∘ b) ≈⟨ ⟺ assoc ⟩
    (f ∘ a) ∘ b ∎

  pushˡ :
    ∀ {f : V ⇒ W} →
    c ∘ f ≈ a ∘ (b ∘ f)
  pushˡ {f = f} = begin
    c ∘ f       ≈⟨ c≡ab ⟩∘⟨refl ⟩
    (a ∘ b) ∘ f ≈⟨ assoc ⟩
    a ∘ (b ∘ f) ∎

open Pushes public

-- Introduce/Elimilate an equivalent-to-identity
-- on left, right or 'in the middle' of something existing
module IntroElim {O} {a : O ⇒ O} (a≡id : a ≈ id) where
  elimʳ :
    ∀ {f : O ⇒ W} →
    f ∘ a ≈ f
  elimʳ {f = f} = begin
    f ∘ a  ≈⟨ refl⟩∘⟨ a≡id ⟩
    f ∘ id ≈⟨ identityʳ ⟩
    f      ∎

  introʳ :
    ∀ {f : O ⇒ W} →
    f ≈ f ∘ a
  introʳ = Equiv.sym elimʳ

  elimˡ :
    ∀ {f : W ⇒ O} →
    (a ∘ f) ≈ f
  elimˡ {f = f} = begin
    a ∘ f  ≈⟨ a≡id ⟩∘⟨refl ⟩
    id ∘ f ≈⟨ identityˡ ⟩
    f      ∎

  introˡ :
    ∀ {f : W ⇒ O} →
    f ≈ a ∘ f
  introˡ = Equiv.sym elimˡ

  intro-center :
    ∀ {f : O ⇒ W} {g : U ⇒ O} →
    f ∘ g ≈ f ∘ (a ∘ g)
  intro-center = ∘-resp-≈ʳ introˡ

  elim-center :
    ∀ {f : O ⇒ W} {g : U ⇒ O} →
    f ∘ (a ∘ g) ≈ f ∘ g
  elim-center = ∘-resp-≈ʳ elimˡ

open IntroElim public

-- given h ∘ f ≈ i ∘ g
module Extends
  {f : A ⇒ B} {g : A ⇒ C} {h : B ⇒ D} {i : C ⇒ D}
  (s : CommutativeSquare f g h i) where
  -- rewrite (a ∘ h) ∘ f to (a ∘ i) ∘ g
  extendˡ :
    ∀ {D′} {a : D ⇒ D′} →
    CommutativeSquare f g (a ∘ h) (a ∘ i)
  extendˡ {a = a} = begin
    (a ∘ h) ∘ f ≈⟨ pullʳ s ⟩
    a ∘ (i ∘ g) ≈⟨ ⟺ assoc ⟩
    (a ∘ i) ∘ g ∎

  -- rewrite h ∘ (f ∘ a) to i ∘ (g ∘ a)
  extendʳ :
    ∀ {A′} {a : A′ ⇒ A} →
    CommutativeSquare (f ∘ a) (g ∘ a) h i
  extendʳ {a = a} = begin
    h ∘ (f ∘ a) ≈⟨ pullˡ s ⟩
    (i ∘ g) ∘ a ≈⟨ assoc ⟩
    i ∘ (g ∘ a) ∎

  -- rewrite (a ∘ h) ∘ (f ∘ b) to (a ∘ i) ∘ (g ∘ b)
  extend² :
    ∀ {A′ D′} {b : A′ ⇒ A} {a : D ⇒ D′} →
    CommutativeSquare (f ∘ b) (g ∘ b) (a ∘ h) (a ∘ i)
  extend² {b = b} {a = a } = begin
    (a ∘ h) ∘ (f ∘ b) ≈⟨ pullʳ extendʳ ⟩
    a ∘ (i ∘ (g ∘ b)) ≈⟨ ⟺ assoc ⟩
    (a ∘ i) ∘ (g ∘ b) ∎

open Extends public

-- essentially composition in the arrow category
{-
   A₁ -- c --> B₁
   |           |
   b′  comm    b
   |           |
   V           V
   A₂ -- c′ -> B₂
   |           |
   a′  comm    a
   |           |
   V           V
   A₃ -- c″ -> B₃

   then the whole diagram commutes
-}
glue :
  ∀ {A₁ A₂ A₃ : 𝒬 .Ob} {B₁ B₂ B₃ : 𝒬 .Ob}
    {a  : B₂ ⇒ B₃} {a′ : A₂ ⇒ A₃}
    {b  : B₁ ⇒ B₂} {b′ : A₁ ⇒ A₂}
    {c  : A₁ ⇒ B₁} {c′ : A₂ ⇒ B₂} {c″ : A₃ ⇒ B₃} →
  CommutativeSquare c′ a′ a c″ →
  CommutativeSquare c b′ b c′ →
  CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
glue {a = a} {a′ = a′} {b = b} {b′ = b′} {c = c} {c′ = c′} {c″ = c″} sq-a sq-b = begin
  (a ∘ b) ∘ c    ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′)  ≈⟨ extendʳ sq-a ⟩
  c″ ∘ (a′ ∘ b′) ∎

-- A "rotated" version of glue′. Equivalent to 'Equiv.sym (glue (Equiv.sym sq-a) (Equiv.sym sq-b))'
glue′ :
  ∀ {A₁ A₂ A₃ : 𝒬 .Ob} {B₁ B₂ B₃ : 𝒬 .Ob}
    {a  : B₂ ⇒ B₃} {a′ : A₂ ⇒ A₃}
    {b  : B₁ ⇒ B₂} {b′ : A₁ ⇒ A₂}
    {c  : A₁ ⇒ B₁} {c′ : A₂ ⇒ B₂} {c″ : A₃ ⇒ B₃} →
  CommutativeSquare a′ c′ c″ a →
  CommutativeSquare b′ c c′ b →
  CommutativeSquare (a′ ∘ b′) c c″ (a ∘ b)
glue′ {a = a} {a′ = a′} {b = b} {b′ = b′} {c = c} {c′ = c′} {c″ = c″} sq-a sq-b = begin
  c″ ∘ (a′ ∘ b′) ≈⟨ pullˡ sq-a ⟩
  (a ∘ c′) ∘ b′  ≈⟨ extendˡ sq-b ⟩
  (a ∘ b) ∘ c    ∎

-- Various gluings of triangles onto sides of squares
glue◃◽ :
  ∀ {A₁ A₂ : 𝒬 .Ob} {B₁ B₂ B₃ : 𝒬 .Ob}
    {a  : B₂ ⇒ B₃}
    {b  : B₁ ⇒ B₂} {b′ : A₁ ⇒ A₂}
    {c  : A₁ ⇒ B₁} {c′ : A₂ ⇒ B₂}
    {x : A₂ ⇒ B₃} →
  a ∘ c′ ≈ x → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) x
glue◃◽ {a = a} {b = b} {b′ = b′} {c = c} {c′ = c′} {x = x} tri-a sq-b = begin
  (a ∘ b) ∘ c   ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′) ≈⟨ pullˡ tri-a ⟩
  x ∘ b′       ∎

glue◃◽′ :
  ∀ {A₁ A₂ : 𝒬 .Ob} {B₁ B₂ : 𝒬 .Ob}
    {b  : B₁ ⇒ B₂} {b′ : A₁ ⇒ A₂}
    {c  : A₁ ⇒ B₁} {c′ : A₂ ⇒ B₂}
    {X} {x : X ⇒ B₂} {y : B₁ ⇒ X} →
  x ∘ y ≈ b → CommutativeSquare c b′ b c′ → CommutativeSquare (y ∘ c) b′ x c′
glue◃◽′ {b = b} {b′ = b′} {c = c} {c′ = c′} {x = x} {y = y} tri sq = begin
  x ∘ (y ∘ c) ≈⟨ pullˡ tri ⟩
  b ∘ c       ≈⟨ sq ⟩
  c′ ∘ b′     ∎

glue◽◃ :
  ∀ {A₁ A₂ : 𝒬 .Ob} {B₁ B₂ : 𝒬 .Ob}
    {b  : B₁ ⇒ B₂} {b′ : A₁ ⇒ A₂}
    {c  : A₁ ⇒ B₁} {c′ : A₂ ⇒ B₂}
    {X} {x : X ⇒ A₁} {y : X ⇒ A₂} →
  CommutativeSquare c b′ b c′ → b′ ∘ x ≈ y → CommutativeSquare (c ∘ x) y b c′
glue◽◃ {b = b} {b′ = b′} {c = c} {c′ = c′} {x = x} {y = y} sq tri = begin
  b ∘ c ∘ x     ≈⟨ pullˡ sq ⟩
  (c′ ∘ b′) ∘ x ≈⟨ pullʳ tri ⟩
  c′ ∘ y        ∎

glue▹◽ :
  ∀ {A₁ A₂ : 𝒬 .Ob} {B₁ B₂ : 𝒬 .Ob}
    {b  : B₁ ⇒ B₂} {b′ : A₁ ⇒ A₂}
    {c  : A₁ ⇒ B₁} {c′ : A₂ ⇒ B₂}
    {X} {x : X ⇒ A₁} {y : X ⇒ A₂} →
  b′ ∘ x ≈ y → CommutativeSquare c b′ b c′ → CommutativeSquare (c ∘ x) y b c′
glue▹◽ {b = b} {b′ = b′} {c = c} {c′ = c′} {x = x} {y = y} tri sq = begin
  b ∘ c ∘ x     ≈⟨ pullˡ sq ⟩
  (c′ ∘ b′) ∘ x ≈⟨ pullʳ tri ⟩
  c′ ∘ y        ∎

-- essentially composition in the over category
glueTrianglesʳ :
  ∀ {A₁ A₂ : 𝒬 .Ob} {B₁ B₂ : 𝒬 .Ob} {a : A₁ ⇒ A₂} {b : B₁ ⇒ A₁} {c : B₂ ⇒ B₁} {x : B₁ ⇒ A₂} {y} →
  a ∘ b ≈ x → x ∘ c ≈ y → a ∘ (b ∘ c) ≈ y
glueTrianglesʳ {a = a} {b = b} {c = c} {x = x} {y = y} a∘b≡x x∘c≡y = begin
  a ∘ (b ∘ c) ≈⟨ pullˡ a∘b≡x ⟩
  x ∘ c       ≈⟨ x∘c≡y ⟩
  y           ∎

-- essentially composition in the under category
glueTrianglesˡ :
  ∀ {A₁ A₂ : 𝒬 .Ob} {B₁ B₂ : 𝒬 .Ob} {a : B₁ ⇒ A₂} {b : A₁ ⇒ B₁} {c : A₂ ⇒ B₂} {x : A₁ ⇒ A₂} {y : A₁ ⇒ B₂} →
  c ∘ x ≈ y → a ∘ b ≈ x → (c ∘ a) ∘ b ≈ y
glueTrianglesˡ {a = a} {b = b} {c = c} {x = x} {y = y} c∘x≡y a∘b≡x = begin
  (c ∘ a) ∘ b ≈⟨ pullʳ a∘b≡x ⟩
  c ∘ x       ≈⟨ c∘x≡y ⟩
  y           ∎

-- Cancel (or insert) inverses on right/left/middle
module Cancellers {h : X ⇒ Y} {i : Y ⇒ X} (inv : h ∘ i ≈ id) where

  cancelʳ : ∀ {f : Y ⇒ Z} → (f ∘ h) ∘ i ≈ f
  cancelʳ {f = f} = begin
    (f ∘ h) ∘ i ≈⟨ pullʳ inv ⟩
    f ∘ id      ≈⟨ identityʳ ⟩
    f           ∎

  insertʳ : ∀ {f : Y ⇒ Z} → f ≈ (f ∘ h) ∘ i
  insertʳ = ⟺ cancelʳ

  cancelˡ : ∀ {f : W ⇒ Y} → h ∘ (i ∘ f) ≈ f
  cancelˡ {f = f} = begin
    h ∘ (i ∘ f) ≈⟨ pullˡ inv ⟩
    id ∘ f      ≈⟨ identityˡ ⟩
    f           ∎

  insertˡ : ∀ {f : W ⇒ Y} → f ≈ h ∘ (i ∘ f)
  insertˡ = ⟺ cancelˡ

  cancelInner :
    ∀ {f : Y ⇒ Z} {g : W ⇒ Y} →
    (f ∘ h) ∘ (i ∘ g) ≈ f ∘ g
  cancelInner = pullˡ cancelʳ

  insertInner :
    ∀ {f : Y ⇒ Z} {g : W ⇒ Y} →
    f ∘ g ≈ (f ∘ h) ∘ (i ∘ g)
  insertInner = ⟺ cancelInner

open Cancellers public

-- operate in the 'center' instead (like pull/push)
center :
  ∀ {a} {f : Y ⇒ Z} {g : X ⇒ Y} {h : W ⇒ X} {i : V ⇒ W} →
  g ∘ h ≈ a → (f ∘ g) ∘ (h ∘ i) ≈ f ∘ (a ∘ i)
center eq = pullʳ (pullˡ eq)

-- operate on the left part, then the right part
center⁻¹ :
  ∀ {a b} {f : Y ⇒ Z} {g : X ⇒ Y} {h : W ⇒ X} {i : V ⇒ W} →
  f ∘ g ≈ a → h ∘ i ≈ b →  f ∘ ((g ∘ h) ∘ i) ≈ a ∘ b
center⁻¹ {a = a} {b = b} {f = f} {g = g} {h = h} {i = i} eq eq′ = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ pullʳ eq′ ⟩
  f ∘ (g ∘ b)     ≈⟨ pullˡ eq ⟩
  a ∘ b           ∎

-- could be called pull₃ʳ
pull-last :
  ∀ {a} {f : Y ⇒ Z} {g : X ⇒ Y} {h : W ⇒ X} {i : V ⇒ W} →
  h ∘ i ≈ a → (f ∘ g ∘ h) ∘ i ≈ f ∘ g ∘ a
pull-last eq = pullʳ (pullʳ eq)

pull-first :
  ∀ {a} {f : Y ⇒ Z} {g : X ⇒ Y} {h : W ⇒ X} {i : V ⇒ W} →
  f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
pull-first {a = a} {f = f} {g = g} {h = h} {i = i} eq = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ assoc ⟩
  f ∘ g ∘ h ∘ i   ≈⟨ pullˡ eq ⟩
  a ∘ h ∘ i       ∎

pull-center :
  ∀ {a} {f : Y ⇒ Z} {g : X ⇒ Y} {h : W ⇒ X} {i : V ⇒ W} →
  g ∘ h ≈ a → f ∘ (g ∘ (h ∘ i)) ≈ f ∘ (a ∘ i)
pull-center eq = ∘-resp-≈ʳ (pullˡ eq)

push-center :
  ∀ {a} {f : Y ⇒ Z} {g : X ⇒ Y} {h : W ⇒ X} {i : V ⇒ W} →
  g ∘ h ≈ a → f ∘ (a ∘ i) ≈ f ∘ (g ∘ (h ∘ i))
push-center eq = Equiv.sym (pull-center eq)

intro-first :
  ∀ {a : A ⇒ Z} {b : Z ⇒ A} {f : Y ⇒ Z} {g : X ⇒ Y} →
  a ∘ b ≈ id → f ∘ g ≈ a ∘ ((b ∘ f) ∘ g)
intro-first {a = a} {b = b} {f = f} {g = g} eq = begin
  f ∘ g             ≈⟨ introˡ eq ⟩
  (a ∘ b) ∘ (f ∘ g) ≈⟨ pullʳ (⟺ assoc) ⟩
  a ∘ ((b ∘ f) ∘ g) ∎

intro-last :
  ∀ {a : A ⇒ X} {b : X ⇒ A} {f : Y ⇒ Z} {g : X ⇒ Y} →
  a ∘ b ≈ id → f ∘ g ≈ f ∘ (g ∘ a) ∘ b
intro-last {a = a} {b = b} {f = f} {g = g} eq = begin
  f ∘ g           ≈⟨ introʳ eq ⟩
  (f ∘ g) ∘ a ∘ b ≈⟨ pullʳ (⟺ assoc) ⟩
  f ∘ (g ∘ a) ∘ b ∎
