{-# OPTIONS --without-K --cubical #-}

module Algebra.OPAS.Base where

open import Prelude
open import Relation.Binary.Preorder
open import Function.Partial


private
  variable
    n m : ℕ

record IsOPAS (𝓥 : Universe) {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor isopas
  infixl 7 _•_
  infix  9 `_ ᶜ_
  infixl 7 _⊙_

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

  data Term (n : ℕ) : 𝓤 ̇ where
    ᶜ_  : A      → Term n
    `_  : Fin n  → Term n
    _⊙_ : Term n → Term n → Term n

  ⟦_⟧_ : {n : ℕ} → Term n → (Fin n → A) → ℒ 𝓥 A
  ⟦ ᶜ a   ⟧ σ = pure a
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

record OpasStr 𝓥 (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor passtr
  field
    _≼_    : Order A 𝓥
    _·_    : A → A → ℒ 𝓥 A
    isOPAS : IsOPAS 𝓥 _≼_ _·_

  infix  4 _≼_
  infixl 7 _·_
  open IsOPAS isOPAS public

-- OPAS stands for Preordered Partial Applicative Structure
OPAS : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
OPAS 𝓥 𝓤 = TypeWithStr 𝓤 (OpasStr 𝓥) 

OPAS₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
OPAS₀ 𝓥 = OPAS 𝓥 𝓤₀

module ≼-Reasoning (𝔄 : OPAS 𝓥 𝓤) where
  open OpasStr (str 𝔄)
    renaming (⟦_⟧_ to ⟦_⟧ᵗ_)

  private
    A = ⟨ 𝔄 ⟩
    variable
      s t u v : Term n
      ρ σ τ : Fin n → A

  infix 4 _under_IsRelatedTo_under_
  infix  1 begin_
  infixr 2 step-≼ step-≡
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

  step-≡ : (s : Term n) (ρ : Fin n → A)
    → t under σ IsRelatedTo u under τ → ⟦ s ⟧ᵗ ρ ≡ ⟦ t ⟧ᵗ σ
    → s under ρ IsRelatedTo u under τ
  step-≡ {u = u} {τ = τ} s ρ (nonstrict y≼z) x≡y = nonstrict (transport (cong (λ a → a ℒ≼ (⟦ u ⟧ᵗ τ)) (sym x≡y)) y≼z)
  step-≡                 s ρ (equals    y≡z) x≡y = equals (x≡y ∙ y≡z) 

  step-≼ : (s : Term n) (ρ : Fin n → A)
    → t under σ IsRelatedTo u under τ → ⟦ s ⟧ᵗ ρ ℒ≼ ⟦ t ⟧ᵗ σ
    → s under ρ IsRelatedTo u under τ
  step-≼ {t = t} {σ} {u = u} {τ} s ρ (nonstrict y≼z) x≼y = nonstrict (ℒ≼-isTransitive (⟦ s ⟧ᵗ ρ) (⟦ t ⟧ᵗ σ) (⟦ u ⟧ᵗ τ) x≼y y≼z)
  step-≼ {t = t} {σ} {u = u} {τ} s ρ (equals    y≡z) x≼y = nonstrict (transport (cong (λ a → LHS ℒ≼ a) y≡z) x≼y)
    where
      LHS = ⟦ s ⟧ᵗ ρ

  ⟦_⟧_∎    : (t : Term n)(σ : Fin n → A) → t under σ IsRelatedTo t under σ
  ⟦ t ⟧ σ ∎ = equals refl

record hasSK (𝔄 : OPAS 𝓥 𝓤) : 𝓤 ⊔ 𝓥  ̇ where
  constructor hasski
  open OpasStr (str 𝔄)
  
  field 
    𝑘         : ⟨ 𝔄 ⟩ 
    𝑠         : ⟨ 𝔄 ⟩
    
  𝐾 : Term n
  𝐾 = ᶜ 𝑘
  𝑆 : Term n
  𝑆 = ᶜ 𝑠

  field
    𝑘ab≼a     : ∀ {a b}   → ⟦ 𝐾 ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ℒ≼ (pure a)
    𝑠²↓       : ∀ {a b}   → ⟦ 𝑆 ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ↓
    𝑠abc≼acbc : ∀ {a b c} → ⟦ 𝑆 ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧₀ ℒ≼ ⟦ ᶜ a ⊙ ᶜ c ⊙ (ᶜ b ⊙ ᶜ c) ⟧₀
