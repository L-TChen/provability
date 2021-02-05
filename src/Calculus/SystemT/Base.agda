{-# OPTIONS --without-K --cubical #-}

-- System T

module Calculus.SystemT.Base where

open import Prelude

open import Calculus.Context
open import Calculus.SystemT.Type public
  hiding (module EncodeDecode)
  
open Calculus.Context             public
  hiding (Z)

infix  3 _⊢_

infixr 5 ƛ_
--infix  6 ⟨_,_⟩
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infix  9 `_

Cxt = Context 𝕋

data _⊢_ (Γ : Cxt) : 𝕋 → 𝓤₀ ̇

variable
  Γ Δ Ξ  : Cxt
  
private
  variable
    A B C          : 𝕋
    M N L M′ N′ L′ : Γ ⊢ A

------------------------------------------------------------------------------
-- Typing Rules

data _⊢_ Γ where
  `_
    : A ∈ Γ
      ---------
    → Γ ⊢ A
  ƛ_
    : A , Γ ⊢ B
      ----------------
    → Γ     ⊢ A `→ B
  _·_
    : Γ ⊢ A `→ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B
--  absurd
--    : (A : 𝕋)
--    → Γ ⊢ `⊥
--    → Γ ⊢ A
  ⟨⟩
    : Γ ⊢ `⊤
  _,_
    : Γ ⊢ A 
    → Γ ⊢ B
    → Γ ⊢ A `× B
  projₗ
    : Γ ⊢ A `× B
    → Γ ⊢ A
  projᵣ
    : Γ ⊢ A `× B
    → Γ ⊢ B
  zero
    : Γ ⊢ nat
  suc
    : Γ ⊢ nat
    → Γ ⊢ nat
  prec
    : Γ ⊢ A
    → A , nat , Γ ⊢ A
    → Γ ⊢ nat
    → Γ ⊢ A

Prog : 𝕋 → 𝓤₀ ̇
Prog A = ∅ ⊢ A

#_ : (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup Γ (toWitness n∈Γ)
#_ {Γ = Γ} n {n∈Γ}  =  ` count Γ (toWitness n∈Γ)


------------------------------------------------------------------------------
-- Some combinators

𝐼 : (A : 𝕋) → Γ ⊢ A `→ A
𝐼 A = ƛ # 0

------------------------------------------------------------------------------
-- Variable renaming

rename : Rename Γ Δ
  → Γ ⊢ A
  → Δ ⊢ A
rename ρ (` x)        = ` ρ x
rename ρ (ƛ M)        = ƛ rename (ext ρ) M
rename ρ (M · N)      = rename ρ M · rename ρ N
--rename ρ (absurd A M) = absurd A (rename ρ M)
rename ρ ⟨⟩           = ⟨⟩
rename ρ (M , N)      = (rename ρ M , rename ρ N)
rename ρ (projₗ M)    = projₗ (rename ρ M)
rename ρ (projᵣ N)    = projᵣ (rename ρ N)
rename ρ zero         = zero
rename ρ (suc M)      = suc (rename ρ M)
rename ρ (prec M N L) = prec (rename ρ M) (rename (ext (ext ρ)) N) (rename ρ L)

↑₁_ :   Γ ⊢ A
  → B , Γ ⊢ A
↑₁_ = rename S_
↑_ : ∅ ⊢ A → Γ ⊢ A
↑_ = rename (λ ())

------------------------------------------------------------------------------
-- Substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = (∀ {A} → A ∈ Γ → Δ ⊢ A)

exts
  : Subst Γ Δ
  → Subst (B , Γ) (B , Δ)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Δ
  → Δ ⊢ A
(` x)     ⟪ σ ⟫  = σ x
(ƛ M)     ⟪ σ ⟫  = ƛ M ⟪ exts σ ⟫
(M · N)   ⟪ σ ⟫  = M ⟪ σ ⟫ · N ⟪ σ ⟫
--(absurd A M) ⟪ σ ⟫ = absurd A (M ⟪ σ ⟫)
⟨⟩        ⟪ σ ⟫  = ⟨⟩
(M , N)   ⟪ σ ⟫  = (M ⟪ σ ⟫ , N ⟪ σ ⟫)
(projₗ M) ⟪ σ ⟫  = projₗ (M ⟪ σ ⟫)
(projᵣ M) ⟪ σ ⟫  = projᵣ (M ⟪ σ ⟫)
zero      ⟪ σ ⟫  = zero
suc M     ⟪ σ ⟫  = suc (M ⟪ σ ⟫)
prec M N L ⟪ σ ⟫ = prec (M ⟪ σ ⟫) (N ⟪ exts (exts σ) ⟫) (L ⟪ σ ⟫)

subst-zero
  : Γ ⊢ B
  → Subst (B , Γ) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : B , Γ ⊢ A
     → Γ ⊢ B
     → Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

subst-one-zero
  : Γ ⊢ B
  → Γ ⊢ C
  → Subst (C , B , Γ) Γ
subst-one-zero M N Z       = N
subst-one-zero M N (S Z)   = M
subst-one-zero M N (S S x) = ` x

_[_,_]₂ : C , B , Γ  ⊢ A
        → Γ ⊢ B
        → Γ ⊢ C
        → Γ ⊢ A
L [ M , N ]₂ = L ⟪ subst-one-zero M N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _-→_
data _-→_ {Γ : Cxt} : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : (ƛ M) · N -→ M [ N ]

  β-⟨,⟩projₗ
    : projₗ (M , N) -→ M

  β-⟨,⟩projᵣ
    : projᵣ (M , N) -→ N

  β-rec-zero
    : prec M N zero -→ M

  β-rec-suc
    : prec M N (suc L) -→ N [ L , prec M N L ]₂

  ξ-ƛ
    :   M -→ M′
    → ƛ M -→ ƛ M′

  ξ-·ₗ
    : L -→ L′
      ---------------
    → L · M -→ L′ · M

  ξ-·ᵣ
    : M -→ M′
      ---------------
    → L · M -→ L · M′

  ξ-⟨,⟩ₗ
    : M -→ M′ 
      ---------------
    → (M , N) -→ (M′ , N)

  ξ-⟨,⟩ᵣ
    : N -→ N′ 
      ---------------
    → (M , N) -→ (M , N′)

  ξ-projₗ
    : L -→ L′
    → projₗ L -→ projₗ L′

  ξ-projᵣ
    : L -→ L′
    → projᵣ L -→ projᵣ L′

  ξ-suc
    : M -→ N
    → suc M -→ suc N

  ξ-rec₁
    : M -→ M′
    → prec M N L -→ prec M′ N L

  ξ-rec₂
    : N -→ N′
    → prec M N L -→ prec M N′ L

  ξ-rec₃
    : L -→ L′
    → prec M N L -→ prec M N L′

------------------------------------------------------------------------------
-- Multi-step beta-reduction

module -↠-Reasoning where
  infix  0 begin_
  infix  2 _-↠_
  infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  data _-↠_ {Γ : Cxt} : Γ ⊢ A → Γ ⊢ A → Set where
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
  infixr 2 ≡⟨⟩-syntax
  syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y
  
  -↠-refl : ∀ {M : Γ ⊢ A} → M -↠ M
  -↠-refl = _ ∎
 
  -↠-reflexive : {M N : Γ ⊢ A} → M ≡ N → M -↠ N
  -↠-reflexive {M = M} {N} M=N = transport (cong (λ M → M -↠ N) (sym M=N)) (N ∎)

  -↠-trans
    : ∀ {L}
    → L -↠ M
    → M -↠ N
      ----------
    → L -↠ N
  -↠-trans L-↠M M-↠N = _ -↠⟨ L-↠M ⟩ M-↠N

  ƛ-↠
    : M -↠ M′
    → ƛ M -↠ ƛ M′
  ƛ-↠ (M ∎)                 = ƛ M ∎
  ƛ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    ƛ M -→⟨ ξ-ƛ M→M₁ ⟩ ƛ-↠ M₁-↠M₂

  ·ₗ-↠
    : M -↠ M′
    → M · N -↠ M′ · N
  ·ₗ-↠ (M ∎)                 = M · _ ∎
  ·ₗ-↠ (M -→⟨ M→Mₗ ⟩ Mₗ-↠M₂) =
    M · _ -→⟨ ξ-·ₗ M→Mₗ ⟩ ·ₗ-↠ Mₗ-↠M₂

  ·ᵣ-↠
    : N -↠ N′
    → M · N -↠ M · N′
  ·ᵣ-↠ (N ∎)                 = _ · N ∎
  ·ᵣ-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    _ · N -→⟨ ξ-·ᵣ N→N₁ ⟩ ·ᵣ-↠ N₁-↠N₂

  ·-↠
    : M -↠ M′
    → N -↠ N′
    → M · N -↠ M′ · N′
  ·-↠ M-↠M′ N-↠N′ = begin
    _ · _
      -↠⟨ ·ₗ-↠ M-↠M′ ⟩
    _ · _
      -↠⟨ ·ᵣ-↠ N-↠N′ ⟩
    _ · _ ∎ 

  projₗ-↠
    : L -↠ L′
    → projₗ L -↠ projₗ L′
  projₗ-↠ (L ∎)                 = projₗ L ∎
  projₗ-↠ (L -→⟨ L→L₁ ⟩ L₁-↠L₂) =
    projₗ L -→⟨ ξ-projₗ L→L₁ ⟩ projₗ-↠ L₁-↠L₂

  projᵣ-↠
    : L -↠ L′
    → projᵣ L -↠ projᵣ L′
  projᵣ-↠ (L ∎)                 = projᵣ L ∎
  projᵣ-↠ (L -→⟨ L→L₂ ⟩ L₂-↠L₂) =
    projᵣ L -→⟨ ξ-projᵣ L→L₂ ⟩ projᵣ-↠ L₂-↠L₂

  ⟨,⟩ₗ-↠
    : M -↠ M′
    → (M , N) -↠ (M′ , N)
  ⟨,⟩ₗ-↠ (M ∎)                 = (M , _) ∎
  ⟨,⟩ₗ-↠ (M -→⟨ M→M₁ ⟩ M₁-↠M₂) =
    (M , _) -→⟨ ξ-⟨,⟩ₗ M→M₁ ⟩ ⟨,⟩ₗ-↠ M₁-↠M₂

  ⟨,⟩ᵣ-↠
    : N -↠ N′
    → (M , N) -↠ (M , N′)
  ⟨,⟩ᵣ-↠ (N ∎)                 = (_ , N) ∎
  ⟨,⟩ᵣ-↠ (N -→⟨ N→N₁ ⟩ N₁-↠N₂) =
    (_ , N) -→⟨ ξ-⟨,⟩ᵣ N→N₁ ⟩ ⟨,⟩ᵣ-↠ N₁-↠N₂

  ⟨,⟩-↠
    : M -↠ M′
    → N -↠ N′
    → (M , N) -↠ (M′ , N′)
  ⟨,⟩-↠ M↠M′ N↠N′ = begin
    _ , _
      -↠⟨ ⟨,⟩ₗ-↠ M↠M′ ⟩
    _ , _
      -↠⟨ ⟨,⟩ᵣ-↠ N↠N′ ⟩
    _ , _
      ∎
open -↠-Reasoning using (_-↠_) public

Normal : (M : Γ ⊢ A) → 𝓤₀ ̇
Normal M = ¬ (Σ[ N ꞉ _ ] M -→ N)

data Value : (M : ∅ ⊢ A) → Set where
  ƛ_
    : (N : A , ∅ ⊢ B)
      -------------------
    → Value (ƛ N)

  ⟨⟩
    : Value ⟨⟩

  _,_
    : (M : ∅ ⊢ A)
    → (N : ∅ ⊢ B)
    → Value (M , N)

  zero
    : Value zero

  suc
    : (M : ∅ ⊢ nat)
    → Value (suc M)

------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : ∅ ⊢ A) : Set where
  step
    : M -→ N
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
progress (M , N)     = done (M , N)
progress (projₗ MN) with progress MN
... | step M-→N      = step (ξ-projₗ M-→N)
... | done (_ , _)   = step β-⟨,⟩projₗ
progress (projᵣ MN) with progress MN
... | step M-→N      = step (ξ-projᵣ M-→N)
... | done (M , N)   = step β-⟨,⟩projᵣ
progress zero        = done zero
progress (suc M)     = done (suc M)
progress (prec M N L) with progress L
... | step L-→L′     = step (ξ-rec₃ L-→L′)
... | done zero      = step β-rec-zero
... | done (suc L′)  = step β-rec-suc

------------------------------------------------------------------------------
-- Decidable equality between α-equivalent terms

module EncodeDecode where
  code : (M : Γ ⊢ A) (N : Δ ⊢ B) → 𝓤₀ ̇
  code {Γ} {A} {Δ} {B} (` x) (` y)     =
    (A=B : A ≡ B) → (Γ=Δ : Γ ≡ Δ) → PathP (λ i →  A=B i ∈ Γ=Δ i) x y
  code (ƛ M)          (ƛ N)            = code M N
  code (M₁ · N₁)      (M₂ · N₂)        = code M₁ M₂ × code N₁ N₂
  code ⟨⟩             ⟨⟩               = Unit
  code (M₁ , N₁)      (M₂ , N₂)        = code M₁ M₂ × code N₁ N₂
  code (projₗ M)      (projₗ N)        = code M N
  code (projᵣ M)      (projᵣ N)        = code M N
  code zero           zero             = Unit
  code (suc M)        (suc N)          = code M N
  code (prec M₁ N₁ L₁) (prec M₂ N₂ L₂) = code M₁ M₂ × code N₁ N₂ × code L₁ L₂ 
  code (ƛ M)          N                = ⊥
  code (` x)          _                = ⊥
  code (_ · _)        _                = ⊥
  code ⟨⟩             _                = ⊥
  code (_ , _)        _                = ⊥
  code (projₗ M)      _                = ⊥
  code (projᵣ M)      _                = ⊥
  code zero           _                = ⊥
  code (suc M)        _                = ⊥
  code (prec M M₁ M₂) _                = ⊥

  postulate
    -- TODO: write this up
    r : (M : Γ ⊢ A) → code M M
  -- r : (M : Γ ⊢ A) → code M M
  -- r (` x)   A=B Γ=Δ = {!!}
  -- r (ƛ M)          = r M
  -- r (M · N)        = r M Prelude., r N
  -- r ⟨⟩             = tt
  -- r ⟨ M , N ⟩      = r M Prelude., r N
  -- r (projₗ M)      = r M
  -- r (projᵣ M)      = r M
  -- r zero           = tt
  -- r (suc M)        = r M
  -- r (prec M M₁ M₂) = r M Prelude., r M₁ Prelude., r M₂

  encode : M ≡ N → code M N
  encode {M = M} M=N = transport (cong (code M) M=N) (r M)
open EncodeDecode using (encode)

𝐼·zero≢zero : 𝐼 {Γ = ∅} nat · zero ≢ zero
𝐼·zero≢zero = encode
