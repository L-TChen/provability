{-# OPTIONS --without-K --cubical #-}

{- Stolen from https://github.com/martinescardo/TypeTopology/ -}

module Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          ; Set to Type
          )

variable
 𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe

infix  1 _̇

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤
