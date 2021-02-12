{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Base where

open import Prelude
  hiding (_∘_; _≤?_)

--open import Calculus.Context      public
--  hiding (count)
open import Cubical.Data.Nat.Order.Recursive
open import Calculus.Untyped.Type public
  
infixr 8 ƛ_ ′_
infixl 10 _·_

infixl 11 _[_] _⟪_⟫

------------------------------------------------------------------------------
-- Typing Rules

private
  variable
    n m : ℕ
    
record Fin (n : ℕ) : 𝓤₀ ̇ where
  constructor fin
  field
    k       : ℕ
    ⦃ k<n ⦄ : k < n

pattern fzero   = fin zero
pattern fsucc x = fin (suc x)

fsuc : Fin n → Fin (suc n)
fsuc (fin k) = fin (suc k)

data Λ (n : ℕ) : 𝓤₀ ̇ where
  `_
    : Fin n
      ---------
    → Λ n
  ƛ_
    : Λ (suc n)
      --------------
    → Λ n

  _·_
    : (M N : Λ n)
      -------------
    → Λ n

private
  variable
    M N L M′ N′ L′ : Λ n

#_ : (x : ℕ)
  → ⦃ x<n : x < n ⦄
    --------------------------------
  → Λ n
#_ x ⦃ x<n ⦄  = ` fin x 

instance
  fromNat∈ : HasFromNat (Λ n)
  fromNat∈ {n} = record
    { Constraint = λ x → (x < n)
    ; fromNat    = #_
    }

------------------------------------------------------------------------------
-- Decidable equality between α-equivalent terms

private
  code⊢ : (M N : Λ n) → 𝓤₀ ̇
  code⊢ (` fin k) (` fin l) = code k l
  code⊢ (ƛ M)     (ƛ N)     = code⊢ M N
  code⊢ (M₁ · N₁) (M₂ · N₂) = code⊢ M₁ M₂ × code⊢ N₁ N₂
  code⊢ _               _   = ⊥

  r⊢ : (M : Λ n) → code⊢ M M
  r⊢ (` fin x)   = r x
  r⊢ (ƛ M)   = r⊢ M
  r⊢ (M · N) = r⊢ M , r⊢ N

  decode⊢ : {M N : Λ n} → code⊢ M N → M ≡ N
  decode⊢ {n} {` fin k} {` fin l} c       = {!!}
  decode⊢ {n} {ƛ M}     {ƛ N}     c       = cong  ƛ_ (decode⊢ c)
  decode⊢ {n} {L₁ · M₁} {_ · _}   (c , d) = cong₂ _·_ (decode⊢ c) (decode⊢ d)
instance
  Code⊢ : Code (Λ n)
  Code⊢ = record { code = code⊢ ; r = r⊢ ; decode = decode⊢ }

private
  _≟⊢_ : (M N : Λ n) → Dec (M ≡ N)
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

-- -- instance
-- --   DecEq⊢ : DecEq (Γ ⊢ A)
-- --   _≟_ ⦃ DecEq⊢ ⦄ = _≟⊢_
------------------------------------------------------------------------------
-- Variable renaming

Rename : ℕ → ℕ → 𝓤₀ ̇
Rename n m = Fin n → Fin m

ext : Rename n m → Rename (suc n) (suc m)
ext ρ (fzero )  = fzero
ext ρ (fsucc x) = fsuc (ρ (fin x))

rename : Rename n m
  → Λ n
  → Λ m
rename ρ (` x)   = ` ρ x
rename ρ (ƛ M)   = ƛ rename (ext ρ) M
rename ρ (M · N) = rename ρ M · rename ρ N

-- ↑ᵣ_ : Γ ⊢ A
--     → Γ ⧺ Δ ⊢ A
-- ↑ᵣ M = rename ρ M
--   where
--     ρ : Rename Γ (Γ ⧺ Δ)
--     ρ (Z p) = Z p
--     ρ (S x) = S ρ x

-- ↑ₗ_ : Δ ⊢ A
--     → Γ ⧺ Δ ⊢ A
-- ↑ₗ M = rename ρ M
--   where
--     ρ : Rename Δ (Γ ⧺ Δ)
--     ρ {Γ = ∅}     x = x
--     ρ {Γ = A , Γ} x = S (ρ x)

-- ↑₁_ : Δ ⊢ A
--   → ⋆ , Δ ⊢ A
-- ↑₁_ = ↑ₗ_

------------------------------------------------------------------------------
-- Substitution

Subst : (n m : ℕ) → 𝓤₀ ̇
Subst n m = Fin n → Λ m

exts
  : Subst n       m
  → Subst (suc n) (suc m)
exts σ fzero = 0
exts σ (fsucc n) = rename fsuc (σ (fin n))

_⟪_⟫
  : Λ n
  → Subst n m
  → Λ m
(` x)   ⟪ σ ⟫ = σ x
(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫

subst-zero
  : Λ n
  → Subst (suc n) n
subst-zero N fzero     = N
subst-zero N (fsucc k) = ` fin k

_[_]
  : Λ (suc n)
  → Λ n
  → Λ n
M [ N ] = M ⟪ subst-zero N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 6 _-→_

data _-→_ {n : ℕ} : Λ n → Λ n → 𝓤₀ ̇ where
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

---------------------------------------------------------------------------
-- Multi-step beta-reduction

module -↠-Reasoning where
  infix  4 begin_
  infix  6 _-↠_
  infixr 6 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_ ≡⟨⟩-syntax
  infix  7 _∎

  syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

  data _-↠_ {n : ℕ} : Λ n → Λ n → 𝓤₀ ̇ where
    _∎ : (M : Λ n) → M -↠ M

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

  -↠-refl : M -↠ M
  -↠-refl = _ ∎

  -↠-respect-≡ : M ≡ N → M -↠ N
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

{-
data Neutral {n : ℕ} : Λ n → 𝓤₀ ̇
data Normal  {n : ℕ} : Λ n → 𝓤₀ ̇

data Neutral {n} where
  `_  : (x : Fin n)
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

neutral-does-not-reduce : Neutral M → M -→ N → ⊥
normal-does-not-reduce  : Normal M → M -→ N → ⊥

neutral-does-not-reduce (` x) ()
neutral-does-not-reduce (M · N) (ξₗ M-→N) = neutral-does-not-reduce M M-→N
neutral-does-not-reduce (M · N) (ξᵣ M-→N) = normal-does-not-reduce N M-→N

normal-does-not-reduce (′ M) M-→N     = neutral-does-not-reduce M M-→N
normal-does-not-reduce (ƛ M) (ζ M-→N) = normal-does-not-reduce M M-→N
------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : Λ n) : 𝓤₀ ̇ where
  step
    : M -→ N
      ----------
    → Progress M

  done
    : Normal M
    → Progress M

progress : (M : Λ n) → Progress M
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
-}

