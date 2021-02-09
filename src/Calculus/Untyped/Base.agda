{-# OPTIONS --without-K --cubical #-}

-- System T

module Calculus.Untyped.Base where

open import Prelude

open import Calculus.Context
  hiding (count)
open import Calculus.Untyped.Type public
  
infix  3 _⊢_

infixr 8 ƛ_ ′_
infix  9 `⟨_,_⟩
infixl 10 _·_

infixl 11 _[_] _⟪_⟫

Cxt = Context 𝕋

variable
  Γ Δ Ξ  : Cxt

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
    A B C   : 𝕋
    M N L M′ N′ L′ : Γ ⊢ A


count : {n : ℕ}
  → (p : n < length Γ) → ⋆ ∈ Γ
count {⋆ , _} {zero}    tt = Z
count {⋆ , Γ} {(suc n)} p  = S count p --S count Γ p

#_ : (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ ⋆
#_ n {n∈Γ}  = ` count (toWitness n∈Γ)

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
    ρ Z     = Z
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

↑_ : ∅ ⊢ A → Γ ⊢ A
↑ M = rename (λ ()) M
------------------------------------------------------------------------------
-- Substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = (∀ {A} → A ∈ Γ → Δ ⊢ A)

exts
  : Subst Γ Δ
  → Subst (A , Γ) (A , Δ)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ  ⊢ A
  → Subst Γ Δ
  → Δ ⊢ A
(` x)   ⟪ σ ⟫ = σ x
(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫

subst-zero
  : Γ ⊢ A
  → Subst (A , Γ) Γ
subst-zero N Z     = N
subst-zero N (S x) = ` x

_[_] : B , Γ ⊢ A
     → Γ ⊢ B
     → Γ ⊢ A
M [ N ] = M ⟪ subst-zero N ⟫

------------------------------------------------------------------------------
-- Cut rule

cut : Γ ⊢ A
  → A , Δ ⊢ B
  → Γ ⧺ Δ ⊢ B
cut {Γ} {A} {Δ} M N = N ⟪ σ ⟫
  where
    σ : Subst (A , Δ) (Γ ⧺ Δ)
    σ Z     = ↑ᵣ M
    σ (S x) = ↑ₗ (` x)

------------------------------------------------------------------------------
-- Some combinators

Λ₀ : 𝓤₀ ̇
Λ₀ = ∅ ⊢ ⋆

𝑰 𝑲 𝑻 𝑭 : Λ₀
𝑰 = ƛ # 0
𝑲 = ƛ ƛ # 1
𝑻 = 𝑲
𝑭 = ƛ ƛ # 0

`⟨_,_⟩ : (M N : Λ₀) → Λ₀
`⟨ M , N ⟩ = ƛ # 0 · (↑ₗ M) · (↑ₗ N)

`projₗ : Λ₀ → Λ₀ 
`projₗ M = M · 𝑻

`projᵣ : Λ₀ → Λ₀ 
`projᵣ M = M · 𝑭
------------------------------------------------------------------------------
-- Church endoing of naturals

pre𝒄_ : ℕ → ⋆ , ⋆ , ∅ ⊢  ⋆
pre𝒄 zero    = # 0
pre𝒄 (suc n) = # 1 · pre𝒄 n

𝒄_ : ℕ → Λ₀
𝒄 n = ƛ ƛ pre𝒄 n 
------------------------------------------------------------------------------
-- Single-step reduction

infix 6 _-→_
data _-→_ {Γ : Cxt} : {A : 𝕋} → Γ ⊢ A → Γ ⊢ A → Set where
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

------------------------------------------------------------------------------
-- Normal terms

data Neutral {Γ : Cxt} : Γ ⊢ A → 𝓤₀ ̇
data Normal  {Γ : Cxt} : Γ ⊢ A → 𝓤₀ ̇

data Neutral {Γ} where
  `_  : (x : A ∈ Γ)
      -------------
    → Neutral (` x)
  _·_ 
    : Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)

data Normal where
  ′_
    : Neutral M
      ---------
    → Normal M
  ƛ_ 
    : Normal N
      ------------
    → Normal (ƛ N)

#′_ : (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Neutral {Γ} (#_ n {n∈Γ})
#′_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

neutral-does-not-reduce : Neutral M → M -→ N → ⊥
normal-does-not-reduce  : Normal M → M -→ N → ⊥

neutral-does-not-reduce (` x) ()
neutral-does-not-reduce (M · N) (ξₗ M-→N) = neutral-does-not-reduce M M-→N
neutral-does-not-reduce (M · N) (ξᵣ M-→N) = normal-does-not-reduce N M-→N

normal-does-not-reduce (′ M) M-→N     = neutral-does-not-reduce M M-→N
normal-does-not-reduce (ƛ M) (ζ M-→N) = normal-does-not-reduce M M-→N
------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : Γ ⊢ A) : Set where
  step
    : M -→ N
      ----------
    → Progress M

  done
    : Normal M
    → Progress M

progress : (M : Γ ⊢ A) → Progress M
progress (` x)                                 =  done (′ ` x )
progress (ƛ N)  with  progress N
... | step N—→N′                               =  step (ζ N—→N′)
... | done NrmN                                =  done (ƛ NrmN)
progress (` x · M) with progress M
... | step M—→M′                               =  step (ξᵣ M—→M′)
... | done NrmM                                =  done (′ (` x) · NrmM)
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L—→L′                               =  step (ξₗ L—→L′)
... | done (′ NeuL) with progress M
...    | step M—→M′                            =  step (ξᵣ M—→M′)
...    | done NrmM                             =  done (′ NeuL · NrmM)

------------------------------------------------------------------------------
-- Decidable equality between α-equivalent terms

module EncodeDecode where
  code : (M : Γ ⊢ A) (N : Δ ⊢ B) → 𝓤₀ ̇
  code {Γ} {A} {Δ} {B} (` x) (` y)     =
    (A=B : A ≡ B) → (Γ=Δ : Γ ≡ Δ) → PathP (λ i →  A=B i ∈ Γ=Δ i) x y
  code (ƛ M)           (ƛ N)            = code M N
  code (M₁ · N₁)       (M₂ · N₂)        = code M₁ M₂ × code N₁ N₂
  code _               _               = ⊥

  postulate
    -- TODO: write this up
    r : (M : Γ ⊢ A) → code M M
  -- r : (M : Γ ⊢ A) → code M M
  -- r (` x)   A=B Γ=Δ = {!!}
  -- r (ƛ M)          = r M
  -- r (M · N)        = r M Prelude., r N

  encode : M ≡ N → code M N
  encode {M = M} M=N = transport (cong (code M) M=N) (r M)
open EncodeDecode using (encode)
