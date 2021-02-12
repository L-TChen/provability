{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Base where

open import Prelude
  hiding (_∘_)

open import Calculus.Context      public
  hiding (count)
open import Calculus.Untyped.Type public
  
infix  3 _⊢_

infixr 8 ƛ_
infixl 10 _·_

infixl 11 _[_] _⟪_⟫

Cxt = Context 𝕋

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ (Γ : Cxt) : 𝕋 → 𝓤₀ ̇ where
  `_ : {A : 𝕋}
    → A ∈ Γ
      ---------
    → Γ ⊢ A
  ƛ_
    : ⋆ , Γ ⊢ ⋆
      --------------
    → Γ     ⊢ ⋆

  _·_
    : Γ ⊢ ⋆ → Γ ⊢ ⋆
      -------------
    → Γ ⊢ ⋆

private
  variable
    A B C          : 𝕋
    Γ Δ Ξ          : Cxt
    M N L M′ N′ L′ : Γ ⊢ A

count : {n : ℕ}
  → (p : n < length Γ) → ⋆ ∈ Γ
count {⋆ , _} {zero}    tt = Z refl
count {⋆ , Γ} {(suc n)} p  = S count p

instance
  fromNat∈ : HasFromNat (Γ ⊢ ⋆)
  fromNat∈ {Γ} = record
    { Constraint = λ n → True (suc n ≤? length Γ)
    ; fromNat    = λ n ⦃ n∈Γ ⦄ → ` count (toWitness n∈Γ) 
    }

------------------------------------------------------------------------------
-- Decidable equality between α-equivalent terms

private
  code⊢ : (M : Γ ⊢ A) (N : Γ ⊢ A) → 𝓤₀ ̇
  code⊢ (` x)     (` y)     = code x y
  code⊢ (ƛ M)     (ƛ N)     = code⊢ M N
  code⊢ (M₁ · N₁) (M₂ · N₂) = code⊢ M₁ M₂ × code⊢ N₁ N₂
  code⊢ _               _   = ⊥

  r⊢ : (M : Γ ⊢ A) → code⊢ M M
  r⊢ (` x)   = r x
  r⊢ (ƛ M)   = r⊢ M
  r⊢ (M · N) = r⊢ M , r⊢ N

  decode⊢ : code⊢ M N → M ≡ N
  decode⊢ {M = ` x}     {` y} c       = cong `_ (decode c)
  decode⊢ {M = ƛ M}     {ƛ N} c       = cong ƛ_ (decode⊢ c)
  decode⊢ {M = _ · _} {_ · _} (c , d) = cong₂ _·_ (decode⊢ c) (decode⊢ d)

instance
  Code⊢ : Code (Γ ⊢ A)
  Code⊢ = record { code = code⊢ ; r = r⊢ ; decode = decode⊢ }

private
  _≟⊢_ : (M N : Γ ⊢ A) → Dec (M ≡ N)
  (` x)     ≟⊢ (` y) with x ≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ x=y → ¬p (decode (encode x=y))
  (ƛ M)     ≟⊢ (ƛ N) with M ≟⊢ N
  ... | yes p = yes (cong ƛ_ p)
  ... | no ¬p = no λ ƛM=ƛN → ¬p (decode (encode ƛM=ƛN))
  (M₁ · N₁) ≟⊢ (M₂ · N₂) with M₁ ≟⊢ M₂ | N₁ ≟⊢ N₂
  ... | yes p | yes q = yes (decode (encode p , encode q))
  ... | yes p | no ¬q = no λ M=N → ¬q (decode (encode M=N .snd))
  ... | no ¬p | q     = no λ M=N → ¬p (decode (encode M=N .fst))
  (` _)   ≟⊢ (ƛ _)    = no encode
  (` _)   ≟⊢ (_ · _)  = no encode
  (ƛ _)   ≟⊢ (` _)    = no encode
  (ƛ _)   ≟⊢ (_ · _)  = no encode
  (_ · _) ≟⊢ (` _)    = no encode
  (_ · _) ≟⊢ (ƛ _)    = no encode

instance
  DecEq⊢ : DecEq (Γ ⊢ A)
  _≟_ ⦃ DecEq⊢ ⦄ = _≟⊢_
------------------------------------------------------------------------------
-- Variable renaming

rename : Rename Γ Δ
  → Γ ⊢ A
  → Δ ⊢ A
rename ρ (` x)   = ` ρ x
rename ρ (ƛ M)   = ƛ rename (ext ρ) M
rename ρ (M · N) = rename ρ M · rename ρ N

↑ᵣ_ : Γ ⊢ A
    → Γ ⧺ Δ ⊢ A
↑ᵣ M = rename ρ M
  where
    ρ : Rename Γ (Γ ⧺ Δ)
    ρ (Z p) = Z p
    ρ (S x) = S ρ x

↑ₗ_ : Δ ⊢ A
    → Γ ⧺ Δ ⊢ A
↑ₗ M = rename ρ M
  where
    ρ : Rename Δ (Γ ⧺ Δ)
    ρ {Γ = ∅}     x = x
    ρ {Γ = A , Γ} x = S (ρ x)

↑₁_ : Δ ⊢ A
  → ⋆ , Δ ⊢ A
↑₁_ = ↑ₗ_

------------------------------------------------------------------------------
-- Substitution

Subst : Cxt → Cxt → 𝓤₀ ̇
Subst Γ Δ = (∀ {A} → A ∈ Γ → Δ ⊢ A)

exts
  : Subst Γ Δ
  → Subst (A , Γ) (A , Δ)
exts σ (Z p) = ` Z p
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Δ
  → Δ ⊢ A
(` x)   ⟪ σ ⟫ = σ x
(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫

subst-zero
  : Γ ⊢ B
  → Subst (B , Γ) Γ
subst-zero N (Z {⋆} {⋆} p) = N
subst-zero _ (S x)         = ` x

_[_]
  : B , Γ ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 6 _-→_
data _-→_ {Γ : Cxt} : {A : 𝕋} → Γ ⊢ A → Γ ⊢ A → 𝓤₀ ̇ where
  β : (ƛ M) · N -→ M [ N ]
  ζ
    :   M -→ M′
    → ƛ M -→ ƛ M′
  ξₗ
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξᵣ
    : M -→ M′
      ---------------
    → L · M -→ L · M′

------------------------------------------------------------------------------
-- Multi-step beta-reduction

module -↠-Reasoning where
  infix  4 begin_
  infix  6 _-↠_
  infixr 6 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_ ≡⟨⟩-syntax
  infix  7 _∎
  
  syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

  data _-↠_ {Γ : Cxt} : Γ ⊢ A → Γ ⊢ A → 𝓤₀ ̇ where
    _∎ : (M : Γ ⊢ A) → M -↠ M

    _-→⟨_⟩_
      : ∀ L
      → L -→ M
      → M -↠ N
        ----------
      → L -↠ N
  begin_
    : M -↠ N
    → M -↠ N
  begin M-↠N = M-↠N

  _-↠⟨_⟩_
    : ∀ L
    → L -↠ M
    → M -↠ N
    → L -↠ N
  M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
  L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

  _≡⟨_⟩_
    : ∀ L
    → L ≡ M
    → M -↠ N
    → L -↠ N
  _≡⟨_⟩_ {M = M}{N = N} L L=M M-↠N = transport (cong (λ M → M -↠ N) (L=M ⁻¹)) M-↠N

  ≡⟨⟩-syntax : ∀ L → L ≡ M → M -↠ N → L -↠ N
  ≡⟨⟩-syntax = _≡⟨_⟩_
  
  -↠-refl : ∀ {M : Γ ⊢ A} → M -↠ M
  -↠-refl = _ ∎
 
  -↠-respect-≡ : {M N : Γ ⊢ A} → M ≡ N → M -↠ N
  -↠-respect-≡ {M = M} {N} M=N = transport (cong (λ M → M -↠ N) (sym M=N)) (N ∎)

  -→to-↠ : M -→ N → M -↠ N
  -→to-↠ M-→N = _ -→⟨ M-→N ⟩ _ ∎ 

  -↠-trans
    : ∀ {L}
    → L -↠ M
    → M -↠ N
      ----------
    → L -↠ N
  -↠-trans L-↠M M-↠N = _ -↠⟨ L-↠M ⟩ M-↠N

  ƛ-cong
    : M -↠ M′
    → ƛ M -↠ ƛ M′
  ƛ-cong (M ∎)                 = ƛ M ∎
  ƛ-cong (M -→⟨ M→M₁ ⟩ M₁-↠M₂) = begin
    ƛ M
      -→⟨ ζ M→M₁ ⟩
    ƛ-cong M₁-↠M₂

  ·ₗ-cong
    : M -↠ M′
    → M · N -↠ M′ · N
  ·ₗ-cong (M ∎)                 = M · _ ∎
  ·ₗ-cong (M -→⟨ M→Mₗ ⟩ Mₗ-↠M₂) =
    M · _ -→⟨ ξₗ M→Mₗ ⟩ ·ₗ-cong Mₗ-↠M₂

  ·ᵣ-cong
    : N -↠ N′
    → M · N -↠ M · N′
  ·ᵣ-cong (N ∎)                 = _ · N ∎
  ·ᵣ-cong (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    _ · N -→⟨ ξᵣ N→N₁ ⟩ ·ᵣ-cong N₁-↠N₂

  ·-cong
    : M -↠ M′
    → N -↠ N′
    → M · N -↠ M′ · N′
  ·-cong M-↠M′ N-↠N′ = begin
    _ · _
      -↠⟨ ·ₗ-cong M-↠M′ ⟩
    _ · _
      -↠⟨ ·ᵣ-cong N-↠N′ ⟩
    _ · _ ∎ 
open -↠-Reasoning using (_-↠_; -↠-refl; -↠-trans; -→to-↠) public
