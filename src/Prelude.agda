{-# OPTIONS --without-K --cubical #-}

module Prelude where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          ; Set to Type
          )
open import Cubical.Foundations.Everything       public
open import Cubical.Data.Sigma                   public
open import Cubical.HITs.PropositionalTruncation public


variable
  𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe

infix 1 _̇

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤

variable
  X Y Z : 𝓤 ̇

Π : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {X = X} Y = (x : X) → Y x
