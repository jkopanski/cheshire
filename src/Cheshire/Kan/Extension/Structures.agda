{-# OPTIONS --safe #-}
open import Cheshire.Core

module Cheshire.Kan.Extension.Structures where

import Cheshire.Category as Category renaming (IsCategory to Structure)
import Cheshire.Morphism.Structures as Morphisms
import Cheshire.Morphism.Bundles as MorphismBundles
import Cheshire.Natural.Signatures as Natural

open import Cheshire.Natural.Signatures
open import Cheshire.Homomorphism.Signatures renaming (_∘_ to _∘F_)

