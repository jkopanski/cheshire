{-# OPTIONS --safe #-}

module Cheshire.Natural where

module Signatures where
  open import Cheshire.Natural.Signatures public

open import Cheshire.Natural.Structures public
open import Cheshire.Natural.Bundles public

import Cheshire.Natural.Equivalence as Eq
module Equivalence = Eq

open Signatures using (_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_) public
