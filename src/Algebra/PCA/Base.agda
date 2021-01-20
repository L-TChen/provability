{-# OPTIONS --without-K --cubical #-}

module Algebra.PCA.Base where
open import Cubical.Foundations.Structure

open import Prelude
open import Function.Partial               public

record PasStr (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor passtr
  field
    _·_    : A → A → ℒ 𝓥 A
    _isSet : isSet A
  infixl 7 _·_

PAS : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PAS 𝓥 𝓤 = TypeWithStr 𝓤 (PasStr 𝓥) 

PAS₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PAS₀ 𝓥 = PAS 𝓥 𝓤₀

record IsPCA (𝓥 : Universe) {A : 𝓤 ̇} (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor ispca
  field
    nonEmpty : ∥ A ∥
    k        : ∥ A ∥
     -- ∃[ k ∈ A ] ∀ (x y : A) → (k · x · y) ↓ ∧ k · x · y = x
    s        : ∥ A ∥
     -- ∃[ s ∈ A ] ∀ (x y z : A) → s · x · y ↓ ∧ s · x · y · z ≳ x · z · (y · z)
    _isSet   : isSet A

  postulate
    i : ∃[ i ꞉ A ] Π[ a ꞉ A ] Σ[ p ꞉ i · a ↓ ] value (i · a) p ≡ a

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
