{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

module Algebra.PCA.Base where

open import Prelude
open import Cubical.Data.Unit
open import Cubical.Foundations.Structure

open import Function.Partial              public

record PasStr (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor passtr
  field
    _·_ : A → A → ℒ 𝓥 A
  infixl 7 _·_

PAS : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PAS 𝓥 𝓤 = TypeWithStr {𝓤 ⊔ 𝓥 ⁺} 𝓤 (PasStr 𝓥) 

PAS₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PAS₀ 𝓥 = PAS 𝓥 𝓤₀

record IsPCA (𝓥 : Universe) {A : 𝓤 ̇} (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ̇ where
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

record PcaStr (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor pcastr
  field
    _·_   : A → A → ℒ 𝓥 A
    isPCA : IsPCA 𝓥 _·_
  infixl 7 _·_
  
PCA : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PCA 𝓥 𝓤 = TypeWithStr 𝓤 (PcaStr 𝓥)

PCA₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PCA₀ 𝓥 = PCA 𝓥 𝓤₀
