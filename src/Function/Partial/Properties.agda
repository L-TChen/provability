{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

module Function.Partial.Properties where

open import Prelude
open import Cubical.Functions.Embedding

open import Function.Partial.Base

partial-map-classifer : {X : Type ℓ₁} {Y : Type ℓ₂}
  → (X ⇀ Y) ≃ (X → ℒ Y)
partial-map-classifer = {!!}
