{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

module Algebra.PCA.Base where

open import Prelude
open import Cubical.Foundations.Structure

open import Function.Partial

record PasStr (A : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor passtr
  field
    _·_ : A → A → ℒ A
  infixl 7 _·_

PAS : (ℓ : Level) → Type (ℓ-suc ℓ)
PAS ℓ = TypeWithStr ℓ PasStr

PAS₀ : Type₁
PAS₀ = PAS ℓ-zero

record IsPCA {A : Type ℓ} (_·_ : A → A → ℒ A) : Type ℓ where
  constructor ispca
  field
    k : {!!} -- ∃[ k ∈ A ] ∀ (x y : A) → (k · x · y) ↓ ∧ k · x · y = x
    s : {!!} -- ∃[ s ∈ A ] ∀ (x y z : A) → s · x · y ↓ ∧ s · x · y · z ≈ x · z · (y · z)
             -- where ≈ is the Kleene equality. Note that k and s are part of properties instead of structure. 

record PcaStr (A : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor pcastr
  field
    _·_   : A → A → ℒ A
    isPCA : IsPCA _·_
  infixl 7 _·_

  open IsPCA isPCA
  
PCA : (ℓ : Level) → Type (ℓ-suc ℓ)
PCA ℓ = TypeWithStr ℓ PcaStr

PCA₀ : Type₁
PCA₀ = PCA ℓ-zero
