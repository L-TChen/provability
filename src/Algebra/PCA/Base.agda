{-# OPTIONS --without-K --cubical #-}

module Algebra.PCA.Base where
open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc)
open import Cubical.Data.Fin as F
  using (Fin; fzero; fsuc)

open import Prelude
open import Function.Partial               public
open import Relation.Binary.Preorder       public

private
  variable
    A   : 𝓤 ̇
    n m : ℕ

record IsPPAS (𝓥 : Universe) {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor ispas
  infix 5 _≼ᵖ_
  infix 7 _•_ _⊙_

  _≼ᵖ_ = ℒᵖ _≼_

  field
    ·-respect-≼  : (x₁ y₁ x₀ y₀ : A) → x₀ ≼ x₁ → y₀ ≼ y₁ → x₀ · y₀ ≼ᵖ x₁ · y₁
    isPreordered : IsPreordered _≼_
    AisSet       : isSet A

  _•_ : ℒ 𝓥 A → ℒ 𝓥 A → ℒ 𝓥 A
  a₁ • a₂ = join ⦇ a₁ · a₂ ⦈
  
  data Term (n : ℕ) : 𝓤  ̇ where
    ᵒ_  : A      → Term n
    ‵_  : Fin n  → Term n
    _⊙_ : Term n → Term n → Term n

  ⟦_⟧_ : Term n → (Fin n → A) → ℒ 𝓥 A
  ⟦ ᵒ a   ⟧ σ = pure a
  ⟦ ‵ i   ⟧ σ = pure (σ i)
  ⟦ t ⊙ s ⟧ σ = ⟦ t ⟧ σ • ⟦ s ⟧ σ

  open IsPreordered isPreordered public

record PPasStr 𝓥 (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor passtr
  field
    _·_    : A → A → ℒ 𝓥 A
    _≼_    : Order A 𝓥
    isPPAS : IsPPAS 𝓥 _≼_ _·_

  infixl 7 _·_
  open IsPPAS isPPAS public

-- PPAS stands for Preordered Partial Applicative Structure
PPAS : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PPAS 𝓥 𝓤 = TypeWithStr 𝓤 (PPasStr 𝓥) 

PPAS₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PPAS₀ 𝓥 = PPAS 𝓥 𝓤₀

record IsCombinatoryComplete 𝓥 {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    isPPAS : IsPPAS 𝓥 _≼_ _·_
  open IsPPAS isPPAS public
  field
    completeness : Π[ t ꞉ Term (suc n) ] Σ[ Λt ꞉ Term n ] Π[ σ ꞉ (Fin n → A) ] Π[ a ꞉ A ]
      (⟦ Λt ⟧ σ • pure a) ≼ᵖ ⟦ t ⟧ {!a ? σ!}
  
-- -- record IsPCA (𝓥 : Universe) {A : 𝓤 ̇} (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
-- --   constructor ispca
-- --   field
-- --     nonEmpty : ∥ A ∥
-- --     k        : ∃[ k ꞉ A ] (∀ (x y : A) → {!(pure k • pure x) • pure y!})
-- --      -- ∃[ k ∈ A ] ∀ (x y : A) → (k · x · y) ↓ ∧ k · x · y = x
-- --     s        : ∥ A ∥
-- --      -- ∃[ s ∈ A ] ∀ (x y z : A) → s · x · y ↓ ∧ s · x · y · z ≳ x · z · (y · z)
-- --     _isSet   : isSet A

-- --   postulate
-- --     i : ∃[ i ꞉ A ] Π[ a ꞉ A ] Σ[ p ꞉ i · a ↓ ] value (i · a) p ≡ a

-- -- record PcaStr (𝓥 : Universe) {A : 𝓤 ̇} (𝑨 : PasStr 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
-- --   constructor pcastr
-- --   field
-- --     _·_   : A → A → ℒ 𝓥 A
-- --     isPCA : IsPCA 𝓥 𝑨
-- --   infixl 7 _·_
-- --   open IsPCA isPCA
  
-- -- PCA : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
-- -- PCA 𝓥 𝓤 = TypeWithStr 𝓤 (PcaStr 𝓥)

-- -- PCA₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
-- -- PCA₀ 𝓥 = PCA 𝓥 𝓤₀
