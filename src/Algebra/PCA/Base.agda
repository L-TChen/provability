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

record IsOPAS (𝓥 : Universe) {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
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

record OPasStr 𝓥 (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor passtr
  field
    _·_    : A → A → ℒ 𝓥 A
    _≼_    : Order A 𝓥
    isOPAS : IsOPAS 𝓥 _≼_ _·_

  infix  4 _≼_
  infixl 7 _·_
  open IsOPAS isOPAS public

-- OPAS stands for Preordered Partial Applicative Structure
OPAS : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
OPAS 𝓥 𝓤 = TypeWithStr 𝓤 (OPasStr 𝓥) 

OPAS₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
OPAS₀ 𝓥 = OPAS 𝓥 𝓤₀

record IsOPCA 𝓥 {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    isOPAS : IsOPAS 𝓥 _≼_ _·_
  open IsOPAS isOPAS public
  
  field
    ƛ_           : Term (suc n) ➝ Term n
    completeness : Π[ t ꞉ Term (suc n) ] Π[ a ꞉ A ] Π[ as ꞉ Fin n ➝ A ] 
      ⟦ ƛ t ⟧ as • (pure a) ≼ᵖ ⟦ t ⟧ (a ∷ as)
  infix  5 ƛ_

  iᵗ : Term n
  iᵗ = ƛ 0 ́

  iᵗ↓ : ⟦ iᵗ ⟧ [] ↓
  iᵗ↓ = {!!}
  
  kᵗ : Term n
  kᵗ = ƛ ƛ 0 ́
  k  = ⟦ kᵗ ⟧ []
  
  k↓ : k ↓ 
  k↓ = {!!}

  sᵗ : Term n
  sᵗ = ƛ ƛ ƛ ƛ 0 ́ ⊙ 2 ́ ⊙ (1 ́ ⊙ 2 ́)
  s  = ⟦ sᵗ ⟧ []

  kab≼a : (a b : A)
    → k • (pure a) • (pure b)  ≼ᵖ (pure a)
  kab≼a a b tt* = {!a!}

  sabc≼acbc : (σ : Fin 3 → A) → ⟦ sᵗ ⊙ 0 ́ ⊙ 1 ́ ⊙ 2 ́ ⟧ σ ≼ᵖ ⟦ 0 ́ ⊙ 2 ́ ⊙ (1 ́ ⊙ 2 ́) ⟧ σ
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
    _≼_    : Order A 𝓥
    _·_    : A → A → ℒ 𝓥 A
    isOPCA : IsOPCA 𝓥 _≼_ _·_ 
  infixl 7 _·_
  open IsOPCA isOPCA
  
PPCA : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
PPCA 𝓥 𝓤 = TypeWithStr 𝓤 (PpcaStr 𝓥)

PPCA₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
PPCA₀ 𝓥 = PPCA 𝓥 𝓤₀
