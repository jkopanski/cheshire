-- Copied with minor changes from agda-categories:
-- https://agda.github.io/agda-categories/Categories.Morphism.Reasoning.Iso.html
-- which is licensed under the MIT license.
--   Copyright (c) 2019 Agda Github Community

{-# OPTIONS --safe #-}

open import Cheshire.Core
open import Cheshire.Signatures
open import Cheshire.Structures.Core
import Cheshire.Morphism.Bundles as Bundles
import Cheshire.Morphism.Structures as Structures
import Cheshire.Morphism.Reasoning.Core as MorReasoning

module Cheshire.Morphism.Reasoning.Iso
  {o l} {Q : Quiver o l}
  {C : Category Q }
  {e} ⦃ eq : Equivalence Q e ⦄
  (is-C : IsCategory C)
  where

open Quiver Q using (_⇒_)
open Category C
open IsCategory is-C
open Definitions C
open Bundles C
open HomReasoning

Inv : {A B : Q .Ob} → A ≅ B → B ≅ A
Inv a-is-b = record
    { from = to
    ; to = from
    ; isIso = record { isoˡ = IsIso.isoʳ isIso ; isoʳ = IsIso.isoˡ isIso }
    }
    where
      open _≅_ a-is-b
      open Structures C

module Switch {A B : Q .Ob}(a-is-b : A ≅ B) where
  open _≅_ a-is-b
  open MorReasoning is-C

  switch-fromtoˡ
    : {X : Q .Ob}{h : X ⇒ A}{k : X ⇒ B}
    → from ∘ h ≈ k → h ≈ to ∘ k
  switch-fromtoˡ {h = h} {k = k} hyp = begin
    h ≈⟨ sym (cancelˡ  isoˡ {f = h}) ⟩
    to ∘ (from ∘ h) ≈⟨ refl ⟩∘⟨ hyp ⟩
    to ∘ k ∎

  switch-fromtoʳ
    : {X : Q .Ob}{h : B ⇒ X}{k : A ⇒ X}
    → h ∘ from ≈ k → h ≈ k ∘ to
  switch-fromtoʳ {h = h} {k = k} hyp = begin
    h ≈⟨ sym (cancelʳ isoʳ {f = h}) ⟩
    (h ∘ from) ∘ to ≈⟨ hyp ⟩∘⟨ refl ⟩
    k ∘ to ∎

module SwitchAround {A B : Q .Ob}(a-is-b : A ≅ B) where
  open _≅_ a-is-b

  switch-tofromˡ
    : {X : Q .Ob}{h : X ⇒ B}{k : X ⇒ A}
    → to ∘ h ≈ k → h ≈ from ∘ k
  switch-tofromˡ = Switch.switch-fromtoˡ {A = B} {B = A} (Inv a-is-b)

  switch-tofromʳ
    : {X : Q .Ob}{h : A ⇒ X}{k : B ⇒ X}
    → h ∘ to ≈ k → h ≈ k ∘ from
  switch-tofromʳ = Switch.switch-fromtoʳ {A = B} {B = A} (Inv a-is-b)
