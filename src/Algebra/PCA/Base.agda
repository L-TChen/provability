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
  infix  4 _ℒ≼_
  
  field
    nonEmpty     : ∥ A ∥
    ≼-isPreorder : IsPreorder _≼_
    AisSet       : isSet A

  -- ℒ≼ is the lifted preorder on ℒ A 
  ℒA            = ℒᵖ (A , _≼_  , ≼-isPreorder)
  _ℒ≼_          = HasPreorder._≼_ (str ℒA) 
  ℒ≼-isPreorder = HasPreorder.≼-isPreorder (str ℒA) 

  field
    ·-respect-≼  : {x₁ y₁ x₀ y₀ : A} → x₀ ≼ x₁ → y₀ ≼ y₁ → x₀ · y₀ ℒ≼ x₁ · y₁

  _•_ : ℒ 𝓥 A → ℒ 𝓥 A → ℒ 𝓥 A
  ma₁ • ma₂ = do
    a₁ ← ma₁
    a₂ ← ma₂
    a₁ · a₂

  •ₗ-respect-ℒ≼ : (x₀ x₁ y : ℒ 𝓥 A) → x₀ ℒ≼ x₁  → x₀ • y ℒ≼ x₁ • y
  •ₗ-respect-ℒ≼ _ _ _ x₀≼ᵖx₁ (x₁↓ , y↓ , xy↓) =
    (x₀↓ , y↓ , xz≼yz .fst) , xz≼yz .snd
    where
      x₀↓   = x₀≼ᵖx₁ x₁↓ .fst
      x₀≼x₁ = x₀≼ᵖx₁ x₁↓ .snd
      xz≼yz = ·-respect-≼ x₀≼x₁ (IsPreorder.isReflexive ≼-isPreorder _) xy↓

  •ᵣ-respect-ℒ≼ : (x y₀ y₁ : ℒ 𝓥 A) → y₀ ℒ≼ y₁ → x • y₀ ℒ≼ x • y₁
  •ᵣ-respect-ℒ≼ _ _ _ y₀≼ᵖy₁ (x↓ , y₁↓ , xy↓) =
    (x↓ , y₀↓ , xy≼xz .fst) , xy≼xz .snd
    where
      y₀↓   = y₀≼ᵖy₁ y₁↓ .fst
      y₀≼y₁ = y₀≼ᵖy₁ y₁↓ .snd
      xy≼xz = ·-respect-≼ (IsPreorder.isReflexive ≼-isPreorder _) y₀≼y₁ xy↓

  •-respect-ℒ≼ : (x₀ y₀ x₁ y₁ : ℒ 𝓥 A) → x₀ ℒ≼ x₁ → y₀ ℒ≼ y₁ → x₀ • y₀ ℒ≼ x₁ • y₁
  •-respect-ℒ≼ _ _ _ _ x₀≼ᵖx₁ y₀≼ᵖy₁ (x₁↓ , y₁↓ , xy↓) =
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

  ⟦_⟧₀ : Term 0 → ℒ 𝓥 A
  ⟦ t ⟧₀ = ⟦ t ⟧ []

  open IsPreorder ≼-isPreorder public
    renaming
      ( isReflexive  to ≼-isReflexive
      ; isTransitive to ≼-isTransitive)
  open IsPreorder ℒ≼-isPreorder public
    renaming
      ( ≼-isProp     to ℒ≼-isProp
      ; isReflexive  to ℒ≼-isReflexive
      ; isTransitive to ℒ≼-isTransitive)

record IsOPCA 𝓥 {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    isOPAS : IsOPAS 𝓥 _≼_ _·_
  open IsOPAS isOPAS  public
  field
    ƛ_           : Term (suc n) ➝ Term n
    completeness : ∀ {t : Term (suc n)} {a : A} {as : Fin n → A} →
      ⟦ (ƛ t) ⊙ ᵒ a ⟧ as ℒ≼ ⟦ t ⟧ (a ∷ as)
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

module Term-Reasoning (𝔄 : OPCA 𝓥 𝓤) where
  open OpcaStr (str 𝔄)
    renaming (⟦_⟧_ to ⟦_⟧ᵗ_)
  A = ⟨ 𝔄 ⟩

  private
    variable
      s t u v : Term n
      ρ σ τ : Fin n → A

  infix 4 _under_IsRelatedTo_under_
  infix  1 begin_
  infixr 2 step-≼ 
  infix  3 ⟦_⟧_∎

  syntax step-≼ s ρ t≼u s≼t = ⟦ s ⟧ ρ ≼⟨ s≼t ⟩ t≼u
  syntax step-≡ s ρ t≼u s≼t = ⟦ s ⟧ ρ ≡⟨ s≼t ⟩ t≼u

  data _under_IsRelatedTo_under_ (t : Term n)(σ : Fin n → A)(s : Term m)(τ : Fin m → A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
    nonstrict : (t≼s : ⟦ t ⟧ᵗ σ ℒ≼ ⟦ s ⟧ᵗ τ) → t under σ IsRelatedTo s under τ
    equals    : (t≡s : ⟦ t ⟧ᵗ σ ≡  ⟦ s ⟧ᵗ τ) → t under σ IsRelatedTo s under τ

  begin_ : t under σ IsRelatedTo s under τ → ⟦ t ⟧ᵗ σ ℒ≼ ⟦ s ⟧ᵗ τ
  begin (nonstrict t≼s)                       = t≼s
  begin_ {n} {t} {σ} {m} {s} {τ} (equals t≡s) = transport (cong (λ a → LHS ℒ≼ a) t≡s) (ℒ≼-isReflexive LHS)
    where
      LHS = ⟦ t ⟧ᵗ σ

  step-≡ : (s : Term n) (ρ : Fin n → A) → t under σ IsRelatedTo u under τ → ⟦ s ⟧ᵗ ρ ≡ ⟦ t ⟧ᵗ σ → s under ρ IsRelatedTo u under τ
  step-≡ {u = u} {τ = τ} s ρ (nonstrict y≼z) x≡y = nonstrict (transport (cong (λ a → a ℒ≼ (⟦ u ⟧ᵗ τ)) (sym x≡y)) y≼z)
  step-≡                 s ρ (equals    y≡z) x≡y = equals (x≡y ∙ y≡z) 

  step-≼ : (s : Term n) (ρ : Fin n → A) → t under σ IsRelatedTo u under τ → ⟦ s ⟧ᵗ ρ ℒ≼ ⟦ t ⟧ᵗ σ → s under ρ IsRelatedTo u under τ
  step-≼ {t = t} {σ} {u = u} {τ} s ρ (nonstrict y≼z) x≼y = nonstrict (ℒ≼-isTransitive (⟦ s ⟧ᵗ ρ) (⟦ t ⟧ᵗ σ) (⟦ u ⟧ᵗ τ) x≼y y≼z)
  step-≼ {t = t} {σ} {u = u} {τ} s ρ (equals    y≡z) x≼y = nonstrict (transport (cong (λ a → LHS ℒ≼ a) y≡z) x≼y)
    where
      LHS = ⟦ s ⟧ᵗ ρ

  ⟦_⟧_∎    : (t : Term n)(σ : Fin n → A) → t under σ IsRelatedTo t under σ
  ⟦ t ⟧ σ ∎ = equals refl
