{-# OPTIONS --without-K --cubical #-}

-- System T

module Calculus.SystemT.Base where

open import Prelude
  hiding (_,_; ⟨_⟩; ⟪_⟫; _∎; _≡⟨_⟩_)

open import Calculus.Type           public
open import Calculus.Context        public

infix  3 _⊢_

infixr 5 ƛ_
infix  6 ⟨_,_⟩
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infix  9 `_

Cxt = Context 𝕋

data _⊢_ (Γ : Cxt) : 𝕋 → 𝓤₀ ̇

private
  variable
    Γ Δ            : Cxt
    A B C          : 𝕋
    M N L M′ N′ L′ : Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ Γ where
  `_
    : Γ ∋ A
      ---------
    → Γ ⊢ A
  ƛ_
    : Γ , A ⊢ B
      ----------------
    → Γ     ⊢ A →̇ B
  _·_
    : Γ ⊢ A →̇ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B
  ⟨⟩
    : Γ ⊢ ⊤̇
  ⟨_,_⟩
    : Γ ⊢ A 
    → Γ ⊢ B
    → Γ ⊢ A ×̇ B
  projₗ
    : Γ ⊢ A ×̇ B
    → Γ ⊢ A
  projᵣ
    : Γ ⊢ A ×̇ B
    → Γ ⊢ B
  zero
    : Γ ⊢ ℕ̇
  suc
    : Γ ⊢ ℕ̇
    → Γ ⊢ ℕ̇
  prec
    : Γ ⊢ A
    → (Γ , ℕ̇) , A ⊢ A
    → Γ ⊢ ℕ̇
    → Γ ⊢ A

Prog : 𝕋 → 𝓤₀ ̇
Prog A = ∅ ⊢ A

#_ : (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup Γ (toWitness n∈Γ)
#_ {Γ = Γ} n {n∈Γ}  =  ` count Γ (toWitness n∈Γ)

------------------------------------------------------------------------------
-- Variable renaming

rename : Rename Γ Δ
  → Γ ⊢ A
  → Δ ⊢ A
rename ρ (` x)        = ` ρ x
rename ρ (ƛ M)        = ƛ rename (ext ρ) M
rename ρ (M · N)      = rename ρ M · rename ρ N
rename ρ ⟨⟩           = ⟨⟩
rename ρ ⟨ M , N ⟩    = ⟨ rename ρ M , rename ρ N ⟩
rename ρ (projₗ M)    = projₗ (rename ρ M)
rename ρ (projᵣ N)    = projᵣ (rename ρ N)
rename ρ zero         = zero
rename ρ (suc M)      = suc (rename ρ M)
rename ρ (prec M N L) = prec (rename ρ M) (rename (ext (ext ρ)) N) (rename ρ L)

↑₁_ : Γ ⊢ A → Γ , B ⊢ A
↑₁_ = rename S_
↑_ : ∅ ⊢ A → Γ ⊢ A
↑_ = rename (λ ())

------------------------------------------------------------------------------
-- Substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = (∀ {A} → Γ ∋ A → Δ ⊢ A)

exts
  : Subst Γ Δ
  → Subst (Γ , B) (Δ , B)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Δ
  → Δ ⊢ A
(` x)     ⟪ σ ⟫  = σ x
(ƛ M)     ⟪ σ ⟫  = ƛ M ⟪ exts σ ⟫
(M · N)   ⟪ σ ⟫  = M ⟪ σ ⟫ · N ⟪ σ ⟫
⟨⟩        ⟪ σ ⟫  = ⟨⟩
⟨ M , N ⟩ ⟪ σ ⟫  = ⟨ M ⟪ σ ⟫ , N ⟪ σ ⟫ ⟩
(projₗ M) ⟪ σ ⟫  = projₗ (M ⟪ σ ⟫)
(projᵣ M) ⟪ σ ⟫  = projᵣ (M ⟪ σ ⟫)
zero      ⟪ σ ⟫  = zero
suc M     ⟪ σ ⟫  = suc (M ⟪ σ ⟫)
prec M N L ⟪ σ ⟫ = prec (M ⟪ σ ⟫) (N ⟪ exts (exts σ) ⟫) (L ⟪ σ ⟫)

subst-zero
  : Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
     → Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

subst-one-zero
  : Γ ⊢ B
  → Γ ⊢ C
  → Subst (Γ , B , C) Γ
subst-one-zero M N Z       = N
subst-one-zero M N (S Z)   = M
subst-one-zero M N (S S x) = ` x

_[_,_]₂ : Γ , B , C ⊢ A
        → Γ ⊢ B
        → Γ ⊢ C
        → Γ ⊢ A
L [ M , N ]₂ = L ⟪ subst-one-zero M N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _⊢_-→_
data _⊢_-→_ (Γ : Cxt) : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : Γ ⊢ (ƛ M) · N -→ M [ N ]

  β-⟨,⟩projₗ
    : Γ ⊢ projₗ ⟨ M , N ⟩ -→ M

  β-⟨,⟩projᵣ
    : Γ ⊢ projᵣ ⟨ M , N ⟩ -→ N

  β-rec-zero
    : Γ ⊢ prec M N zero -→ M

  β-rec-suc
    : Γ ⊢ prec M N (suc L) -→ N [ L , prec M N L ]₂

  ξ-ƛ
    : Γ , A ⊢ M -→ M′
    → Γ     ⊢ ƛ M -→ ƛ M′

  ξ-·ₗ
    : Γ ⊢ L -→ L′
      ---------------
    → Γ ⊢ L · M -→ L′ · M

  ξ-·ᵣ
    : Γ ⊢ M -→ M′
      ---------------
    → Γ ⊢ L · M -→ L · M′

  ξ-⟨,⟩ₗ
    : Γ ⊢ M -→ M′ 
      ---------------
    → Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M′ , N ⟩

  ξ-⟨,⟩ᵣ
    : Γ ⊢ N -→ N′ 
      ---------------
    → Γ ⊢ ⟨ M , N ⟩ -→ ⟨ M , N′ ⟩

  ξ-projₗ
    : Γ ⊢ L -→ L′
    → Γ ⊢ projₗ L -→ projₗ L′

  ξ-projᵣ
    : Γ ⊢ L -→ L′
    → Γ ⊢ projᵣ L -→ projᵣ L′

  ξ-suc
    : Γ ⊢ M -→ N
    → Γ ⊢ suc M -→ suc N

  ξ-rec₁
    : Γ ⊢ M -→ M′
    → Γ ⊢ prec M N L -→ prec M′ N L

  ξ-rec₂
    : Γ , ℕ̇ , A ⊢ N -→ N′
    → Γ ⊢ prec M N L -→ prec M N′ L

  ξ-rec₃
    : Γ ⊢ L -→ L′
    → Γ ⊢ prec M N L -→ prec M N L′

------------------------------------------------------------------------------
-- Multi-step beta-reduction

module -↠-Reasoning where
  infix  0 begin_
  infix  2 _⊢_-↠_
  infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  data _⊢_-↠_ (Γ : Cxt) : Γ ⊢ A → Γ ⊢ A → Set where
    _∎ : (M : Γ ⊢ A) → Γ ⊢ M -↠ M

    _-→⟨_⟩_
      : ∀ L
      → Γ ⊢ L -→ M
      → Γ ⊢ M -↠ N
        ----------
      → Γ ⊢ L -↠ N

  begin_
    : Γ ⊢ M -↠ N
    → Γ ⊢ M -↠ N
  begin M-↠N = M-↠N

  _-↠⟨_⟩_
    : ∀ L
    → Γ ⊢ L -↠ M
    → Γ ⊢ M -↠ N
    → Γ ⊢ L -↠ N
  M -↠⟨ M ∎ ⟩ M-↠N                = M-↠N
  L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

  _≡⟨_⟩_
    : ∀ L
    → L ≡ M
    → Γ ⊢ M -↠ N
    → Γ ⊢ L -↠ N
  _≡⟨_⟩_ {Γ = Γ} {M = M}{N = N} L L=M M-↠N = transport (cong (λ M → Γ ⊢ M -↠ N) (L=M ⁻¹)) M-↠N

  -↠-refl : ∀ {M : Γ ⊢ A} → Γ ⊢ M -↠ M
  -↠-refl = _ ∎
 
  -↠-reflexive : {M N : Γ ⊢ A} → M ≡ N → Γ ⊢ M -↠ N
  -↠-reflexive {Γ = Γ} {M = M} {N} M=N = transport (cong (λ M → Γ ⊢ M -↠ N) (sym M=N)) (N ∎)

  -↠-trans
    : ∀ {L}
    → Γ ⊢ L -↠ M
    → Γ ⊢ M -↠ N
      ----------
    → Γ ⊢ L -↠ N
  -↠-trans L-↠M M-↠N = _ -↠⟨ L-↠M ⟩ M-↠N
open -↠-Reasoning using (_⊢_-↠_; -↠-refl; -↠-reflexive; -↠-trans) public


data Value : (M : ∅ ⊢ A) → Set where
  ƛ_
    : (N : ∅ , A ⊢ B)
      -------------------
    → Value (ƛ N)

  ⟨⟩
    : Value ⟨⟩

  ⟨_,_⟩
    : (M : ∅ ⊢ A)
    → (N : ∅ ⊢ B)
    → Value ⟨ M , N ⟩

  zero
    : Value zero

  suc
    : (M : ∅ ⊢ ℕ̇)
    → Value (suc M)

------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : ∅ ⊢ A) : Set where
  step
    : ∅ ⊢ M -→ N
      --------------
    → Progress M

  done
    : Value M
    → Progress M

progress : (M : ∅ ⊢ A) → Progress M
progress (ƛ M)       = done (ƛ M)
progress (M · N)    with progress M | progress N
... | step M→M′   | _         = step (ξ-·ₗ M→M′)
... | _           | step N→N′ = step (ξ-·ᵣ N→N′)
... | done (ƛ M′) | done vN   = step β-ƛ·
progress ⟨⟩          = done ⟨⟩
progress ⟨ M , N ⟩   = done ⟨ M , N ⟩
progress (projₗ MN) with progress MN
... | step M-→N      = step (ξ-projₗ M-→N)
... | done ⟨ _ , _ ⟩ = step β-⟨,⟩projₗ
progress (projᵣ MN) with progress MN
... | step M-→N      = step (ξ-projᵣ M-→N)
... | done ⟨ M , N ⟩ = step β-⟨,⟩projᵣ
progress zero        = done zero
progress (suc M)     = done (suc M)
progress (prec M N L) with progress L
... | step L-→L′     = step (ξ-rec₃ L-→L′)
... | done zero      = step β-rec-zero
... | done (suc L′)  = step β-rec-suc


module _ where
  open -↠-Reasoning

  ƛ-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ ƛ M -↠ ƛ M′
  ƛ-↠ (M ∎)                 = ƛ M ∎
  ƛ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    ƛ M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ-↠ M₁-↠M₂

  ·ₗ-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ M · N -↠ M′ · N
  ·ₗ-↠ (M ∎)                 = M · _ ∎
  ·ₗ-↠ (M -→⟨ M→Mₗ ⟩ Mₗ-↠M₂) =
    M · _ -→⟨ ξ-·ₗ M→Mₗ ⟩ ·ₗ-↠ Mₗ-↠M₂

  ·ᵣ-↠
    : _ ⊢ N -↠ N′
    → _ ⊢ M · N -↠ M · N′
  ·ᵣ-↠ (N ∎)                 = _ · N ∎
  ·ᵣ-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    _ · N -→⟨ ξ-·ᵣ N→N₁ ⟩ ·ᵣ-↠ N₁-↠N₂

  ·-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ N -↠ N′
    → _ ⊢ M · N -↠ M′ · N′
  ·-↠ M-↠M′ N-↠N′ = begin
    _ · _
      -↠⟨ ·ₗ-↠ M-↠M′ ⟩
    _ · _
      -↠⟨ ·ᵣ-↠ N-↠N′ ⟩
    _ · _ ∎ 

  projₗ-↠
    : _ ⊢ L -↠ L′ → _ ⊢ projₗ L -↠ projₗ L′
  projₗ-↠ (L ∎)                 = projₗ L ∎
  projₗ-↠ (L -→⟨ L→L₁ ⟩ L₁-↠L₂) =
    projₗ L -→⟨ ξ-projₗ L→L₁ ⟩ projₗ-↠ L₁-↠L₂

  projᵣ-↠
    : _ ⊢ L -↠ L′
    → _ ⊢ projᵣ L -↠ projᵣ L′
  projᵣ-↠ (L ∎)                 = projᵣ L ∎
  projᵣ-↠ (L -→⟨ L→L₂ ⟩ L₂-↠L₂) =
    projᵣ L -→⟨ ξ-projᵣ L→L₂ ⟩ projᵣ-↠ L₂-↠L₂

  ⟨,⟩ₗ-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N ⟩
  ⟨,⟩ₗ-↠ (M ∎)                 = ⟨ M , _ ⟩ ∎
  ⟨,⟩ₗ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    ⟨ M , _ ⟩ -→⟨ ξ-⟨,⟩ₗ M→M₁ ⟩ ⟨,⟩ₗ-↠ M₁-↠M₂

  ⟨,⟩ᵣ-↠
    : _ ⊢ N -↠ N′
    → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M , N′ ⟩
  ⟨,⟩ᵣ-↠ (N ∎)                 = ⟨ _ , N ⟩ ∎
  ⟨,⟩ᵣ-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    ⟨ _ , N ⟩ -→⟨ ξ-⟨,⟩ᵣ N→N₁ ⟩ ⟨,⟩ᵣ-↠ N₁-↠N₂

  ⟨,⟩-↠
    : _ ⊢ M -↠ M′
    → _ ⊢ N -↠ N′
    → _ ⊢ ⟨ M , N ⟩ -↠ ⟨ M′ , N′ ⟩
  ⟨,⟩-↠ M↠M′ N↠N′ = begin
    ⟨ _ , _ ⟩
      -↠⟨ ⟨,⟩ₗ-↠ M↠M′ ⟩
    ⟨ _ , _ ⟩
      -↠⟨ ⟨,⟩ᵣ-↠ N↠N′ ⟩
    ⟨ _ , _ ⟩
      ∎
