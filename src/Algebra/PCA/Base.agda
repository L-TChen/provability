{-# OPTIONS --without-K --cubical #-}

module Algebra.PCA.Base where
open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc)
import  Cubical.Data.Nat.Order as ℕₚ
open import Cubical.Data.Fin as F
  using (Fin; fzero; fsuc; ¬Fin0)

open import Prelude
open import Function.Partial               public
open import Relation.Binary.Preorder       public

private
  variable
    n m : ℕ
    
infixr 5 _∷_

[] : {A : 𝓤 ̇} → Fin 0 → A
[] {A = A} i = ⊥-elim {A = λ _ → A} (¬Fin0 i)

_∷_ : {A : 𝓤 ̇} → A → (Fin n → A) → Fin (suc n) → A
(a ∷ as) (zero  , 0<n)   = a
(a ∷ as) (suc i , 1+i<n) = as (i , ℕₚ.pred-≤-pred 1+i<n)

record IsOPAS (𝓥 : Universe) {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor isopas
  infix  9 `_ ᵒ_
  infixl 7 _•_ _⊙_
  infix  4 _≼ᵖ_
  
  field
    nonEmpty     : ∥ A ∥
    ≼-isPreorder : IsPreorder _≼_
    AisSet       : isSet A

  -- ≼ᴾ is the lifted preorder on ℒ A 
  ℒA≼           = ℒᵖ (A , _≼_  , ≼-isPreorder)
  _≼ᵖ_          = HasPreorder._≼_ (str ℒA≼) 
  ≼ᵖ-isPreorder = HasPreorder.≼-isPreorder (str ℒA≼) 

  field
    ·-respect-≼  : {x₁ y₁ x₀ y₀ : A} → x₀ ≼ x₁ → y₀ ≼ y₁ → x₀ · y₀ ≼ᵖ x₁ · y₁

  open IsPreorder ≼-isPreorder public
    renaming
      ( isReflexive  to ≼-isReflexive
      ; isTransitive to ≼-isTransitive)
  open IsPreorder ≼ᵖ-isPreorder public
    renaming
      ( ≼-isProp     to ≼ᵖ-isProp
      ; isReflexive  to ≼ᵖ-isReflexive
      ; isTransitive to ≼ᵖ-isTransitive)

  _•_ : ℒ 𝓥 A → ℒ 𝓥 A → ℒ 𝓥 A
  ma₁ • ma₂ = do
    a₁ ← ma₁
    a₂ ← ma₂
    a₁ · a₂
  
  •-respect-≼ᵖ : (x₀ y₀ x₁ y₁ : ℒ 𝓥 A) → x₀ ≼ᵖ x₁ → y₀ ≼ᵖ y₁ → x₀ • y₀ ≼ᵖ x₁ • y₁
  •-respect-≼ᵖ _ _ _ _ x₀≼ᵖx₁ y₀≼ᵖy₁ (x₁↓ , y₁↓ , xy↓) =
    (x₀↓ , y₀↓ , ·-respect-≼ x₀≼x₁ y₀≼y₁ xy↓ .fst) , ·-respect-≼ x₀≼x₁ y₀≼y₁ xy↓ .snd
    where
      x₀↓   = x₀≼ᵖx₁ x₁↓ .fst
      x₀≼x₁ = x₀≼ᵖx₁ x₁↓ .snd
      y₀↓   = y₀≼ᵖy₁ y₁↓ .fst
      y₀≼y₁ = y₀≼ᵖy₁ y₁↓ .snd

  data Term (n : ℕ) : 𝓤  ̇ where
    ᵒ_  : A      → Term n
    `_  : Fin n  → Term n
    _⊙_ : Term n → Term n → Term n

  ⟦_⟧_ : Term n → (Fin n → A) → ℒ 𝓥 A
  ⟦ ᵒ a   ⟧ σ = pure a
  ⟦ ` i   ⟧ σ = pure (σ i)
  ⟦ t ⊙ s ⟧ σ = ⟦ t ⟧ σ • ⟦ s ⟧ σ

  ⟦_⟧₀   : Term 0 → ℒ 𝓥 A
  ⟦ t ⟧₀ = ⟦ t ⟧ []

  ⟦_⟧₁_   : Term 1 → A → ℒ 𝓥 A
  ⟦ t ⟧₁ a = ⟦ t ⟧ (a ∷ [])

record IsOPCA 𝓥 {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    isOPAS : IsOPAS 𝓥 _≼_ _·_
  open IsOPAS isOPAS  public
  field
    ƛ_           : Term (suc n) ➝ Term n
    completeness : Π[ t ꞉ Term (suc n) ] Π[ a ꞉ A ] Π[ as ꞉ Fin n ➝ A ] 
      ⟦ (ƛ t) ⊙ ᵒ a ⟧ as ≼ᵖ ⟦ t ⟧ (a ∷ as)
  infixr  5 ƛ_

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

record OpcaStr (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor opcastr
  field
    _≼_    : Order A 𝓥
    _·_    : A → A → ℒ 𝓥 A
    isOPCA : IsOPCA 𝓥 _≼_ _·_ 
  infixl 7 _·_
  open IsOPCA isOPCA public
  
OPCA : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
OPCA 𝓥 𝓤 = TypeWithStr 𝓤 (OpcaStr 𝓥)

OPCA₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
OPCA₀ 𝓥 = OPCA 𝓥 𝓤₀
