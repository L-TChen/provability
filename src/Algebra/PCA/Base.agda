{-# OPTIONS --without-K --cubical #-}

module Algebra.PCA.Base where
open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _+_)
import  Cubical.Data.Nat.Order as ℕₚ
open import Cubical.Data.Fin as F
  using (Fin; fzero; fsuc; ¬Fin0)

open import Prelude
open import Function.Partial               public
open import Relation.Binary.Preorder       public

private
  variable
    A   : 𝓤 ̇
    n m : ℕ
    
infixr 5 _∷_

[] : Fin 0 → A
[] {A = A} i = ⊥-elim {A = λ _ → A} (¬Fin0 i)

_∷_ : A → (Fin n → A) → Fin (suc n) → A
(a ∷ as) (zero  , 0<n)   = a
(a ∷ as) (suc i , 1+i<n) = as (i , ℕₚ.pred-≤-pred 1+i<n)

0ᶠ = fzero
1ᶠ : Fin (2 + n)
1ᶠ = fsuc 0ᶠ
2ᶠ : Fin (3 + n)
2ᶠ = fsuc 1ᶠ
3ᶠ : Fin (4 + n)
3ᶠ = fsuc 2ᶠ

record IsPPAS (𝓥 : Universe) {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor ispas
  -- ≼ᴾ is the lifted preorder on ℒ A 
  infix 4 _≼ᵖ_
  _≼ᵖ_ = ℒᵖ _≼_
  field
    nonEmpty     : ∥ A ∥
    ·-respect-≼  : (x₁ y₁ x₀ y₀ : A) → x₀ ≼ x₁ → y₀ ≼ y₁ → x₀ · y₀ ≼ᵖ x₁ · y₁
    isPreordered : IsPreordered _≼_
    AisSet       : isSet A

  open IsPreordered isPreordered public

  infix  9 _́ _̂
  infixl 7 _•_ _⊙_

  _•_ : ℒ 𝓥 A → ℒ 𝓥 A → ℒ 𝓥 A
  ma₁ • ma₂ = do
    a₁ ← ma₁
    a₂ ← ma₂
    a₁ · a₂
  
  a•b↓→a↓ : {a b : ℒ 𝓥 A} → a • b ↓ → a ↓
  a•b↓→a↓ (a↓ , _) = a↓

  a•b↓→b↓ : {a b : ℒ 𝓥 A} → a • b ↓ → b ↓
  a•b↓→b↓ (_ , b↓ , _) = b↓
  
  data Term (n : ℕ) : 𝓤  ̇ where
    _̂   : A      → Term n
    _́   : Fin n  → Term n
    _⊙_ : Term n → Term n → Term n

  ⟦_⟧_ : Term n → (Fin n → A) → ℒ 𝓥 A
  ⟦ a ̂    ⟧ σ = pure a
  ⟦ i ́    ⟧ σ = pure (σ i)
  ⟦ t ⊙ s ⟧ σ = ⟦ t ⟧ σ • ⟦ s ⟧ σ

record PPasStr 𝓥 (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor passtr
  field
    _·_    : A → A → ℒ 𝓥 A
    _≼_    : Order A 𝓥
    isPPAS : IsPPAS 𝓥 _≼_ _·_

  infix  4 _≼_
  infixl 7 _·_
  open IsPPAS isPPAS public

-- PPAS stands for Preordered Partial Applicative Structure
PPAS : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PPAS 𝓥 𝓤 = TypeWithStr 𝓤 (PPasStr 𝓥) 

PPAS₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PPAS₀ 𝓥 = PPAS 𝓥 𝓤₀

record IsPPCA 𝓥 {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    isPPAS : IsPPAS 𝓥 _≼_ _·_
  open IsPPAS isPPAS public
  
  field
    ƛ_ : Term (suc n) → Term n
    completeness : Π[ t ꞉ Term (suc n) ] Π[ σ ꞉ (Fin n → A) ] Π[ a ꞉ A ]
      ⟦ ƛ t ⟧ σ • (pure a) ≼ᵖ ⟦ t ⟧ (a ∷ σ)
  infix  5 ƛ_

  iᵗ : Term n
  iᵗ = ƛ 0ᶠ ́
  
  kᵗ : Term n
  kᵗ = ƛ ƛ 0ᶠ ́

  sᵗ : Term n
  sᵗ = ƛ ƛ ƛ ƛ 0ᶠ ́ ⊙ 2ᶠ ́ ⊙ (1ᶠ ́ ⊙ 2ᶠ ́)
  
  iᵗ↓ : ⟦ iᵗ ⟧ [] ↓
  iᵗ↓ = {!!}

  k↓ : ⟦ kᵗ ⟧ [] ↓ 
  k↓ = {!!}

  kab≼a : (a b : A)
    → ⟦ kᵗ ⊙ 0ᶠ ́ ⊙ 1ᶠ ́ ⟧ (a ∷ b ∷ [])  ≼ᵖ ⟦ 0ᶠ ́ ⟧ (a ∷ [])
  kab≼a a b tt* = {!a!}

  sabc≼acbc : (σ : Fin 3 → A) → ⟦ sᵗ ⊙ 0ᶠ ́ ⊙ 1ᶠ ́ ⊙ 2ᶠ ́ ⟧ σ ≼ᵖ ⟦ 0ᶠ ́ ⊙ 2ᶠ ́ ⊙ (1ᶠ ́ ⊙ 2ᶠ ́) ⟧ σ
  sabc≼acbc σ p = {!!} , {!!}

-- record IsPCA (𝓥 : Universe) {A : 𝓤 ̇} (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
--   constructor ispca
--   field
--     nonEmpty : ∥ A ∥
--     k        : ∃[ k ꞉ A ] (∀ (x y : A) → {!(pure k • pure x) • pure y!})
--      -- ∃[ k ∈ A ] ∀ (x y : A) → (k · x · y) ↓ ∧ k · x · y = x
--     s        : ∥ A ∥
--      -- ∃[ s ∈ A ] ∀ (x y z : A) → s · x · y ↓ ∧ s · x · y · z ≳ x · z · (y · z)
--     _isSet   : isSet A

--   postulate
--     i : ∃[ i ꞉ A ] Π[ a ꞉ A ] Σ[ p ꞉ i · a ↓ ] value (i · a) p ≡ a

record PpcaStr (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor ppcastr
  field
    _≼_   : Order A 𝓥
    _·_   : A → A → ℒ 𝓥 A
    isPCA : IsPPCA 𝓥 _≼_ _·_ 
  infixl 7 _·_
  open IsPPCA isPCA
  
PPCA : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PPCA 𝓥 𝓤 = TypeWithStr 𝓤 (PpcaStr 𝓥)

PPCA₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PPCA₀ 𝓥 = PPCA 𝓥 𝓤₀
