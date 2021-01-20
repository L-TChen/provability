{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

module Function.Partial.Properties where

open import Prelude
open import Cubical.Functions.Embedding

open import Function.Partial.Base

partial-map-classifer : {X Y : 𝓤 ̇}
  → (X ⇀ Y) ≃ (X → ℒ (universeOf X ⊔ universeOf Y) Y)
partial-map-classifer = {!!}
