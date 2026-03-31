{-# OPTIONS --safe #-}

open import Cheshire.Core

module Cheshire.Construction.Sub {o ℓ} (𝒰 : Quiver o ℓ) where

import Cheshire.Construction.Sub.Object as Obj
import Cheshire.Construction.Sub.Morphism as Mor

module Object = Obj 𝒰
module Morphism = Mor 𝒰
