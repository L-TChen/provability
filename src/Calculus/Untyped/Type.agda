{-# OPTIONS --without-K --cubical --guarded #-}

module Calculus.Untyped.Type where

open import Prelude

data 𝕋 : 𝓤₀ ̇ where
  ⋆ : 𝕋

instance
  DecEq𝕋 : DecEq 𝕋
  _≟_ ⦃ DecEq𝕋 ⦄ = λ { ⋆ ⋆ → yes refl}
