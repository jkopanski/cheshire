{-# OPTIONS --safe #-}

module Cheshire.Cartesian where

open import Cheshire.Cartesian.Signature public renaming (Cartesian to Signature)
open import Cheshire.Cartesian.Structure public
open import Cheshire.Cartesian.Bundle public
import Cheshire.Cartesian.Transfer as T

module Transfer = T
