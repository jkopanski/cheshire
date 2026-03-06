{-# OPTIONS --safe #-}

-- I have no idea why agda-categories doesn't put this under
-- Construction hierarchy.  I do since I'll need this in the
-- Cheshire.Signatures for the Monoidal.  Also this could construct
-- other structures than Category, like Cartesian, given the inputs
-- have the same structure.  I don't know yet how to untangle those
-- module dependencies.  I might not need it anyway.

open import Cheshire.Core

module Cheshire.Construction.Product where

open import Cheshire.Construction.Product.Signatures public
open import Cheshire.Construction.Product.Structures public
open import Cheshire.Construction.Product.Bundles public renaming (Category to ProductCategory)
