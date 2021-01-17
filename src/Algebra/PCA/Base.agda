{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

module Algebra.PCA.Base where

open import Prelude
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure

open import Function.Partial              public

record PasStr (A : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor passtr
  field
    _·_ : A → A → ℒ A
  infixl 7 _·_

PAS : (ℓ : Level) → Type (ℓ-suc ℓ)
PAS ℓ = TypeWithStr ℓ PasStr

PAS₀ : Type₁
PAS₀ = PAS ℓ-zero

record IsPCA {A : 𝓤 ̇} (_·_ : A → A → ℒ A) : 𝓤 ̇ where
  constructor ispca
  field
    nonEmpty : ∃[ a ∈ A ] Unit
    -- k : {!!}
     -- ∃[ k ∈ A ] ∀ (x y : A) → (k · x · y) ↓ ∧ k · x · y = x
    -- s : {!!}
     -- ∃[ s ∈ A ] ∀ (x y z : A) → s · x · y ↓ ∧ s · x · y · z ≳ x · z · (y · z)
    -- where e ≳ e′ means that if e′ is defined then e is defined and e = e′
  i : Σ[ i ∈ A ] ∀ (x : A) → Σ[ p ∈ (i · x) ↓ ] value (i · x) p ≡ x 
  i = {!!}
  -- i = s · k · k

record PcaStr (A : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor pcastr
  field
    _·_   : A → A → ℒ A
    isPCA : IsPCA _·_
  infixl 7 _·_
  
PCA : (ℓ : Level) → Type (ℓ-suc ℓ)
PCA ℓ = TypeWithStr ℓ PcaStr

PCA₀ : Type₁
PCA₀ = PCA ℓ-zero
