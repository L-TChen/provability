module Calculus.Untyped.Base where

open import Prelude
  hiding (_∘_)

infixr 8  ƛ_
infixl 10 _·_

infixl 11 _[_] _⟪_⟫

------------------------------------------------------------------------------
-- Typing Rules

data Λ (n : ℕ) : 𝓤₀ ̇ where
  `_ : (x : Fin n) → Λ n

  ƛ_ : Λ (suc n)
     → Λ n

  _·_
    : (M N : Λ n)
    → Λ n

private
  variable
    n m l          : ℕ
    M N L M′ N′ L′ Γ Δ : Λ n

Λ₀ = Λ 0
Λ₁ = Λ 1
Λ₂ = Λ 2

count : {n i : ℕ}
  → (p : i < n) → Fin n
count {zero}  ()
count {suc n} {zero}  tt = fzero
count {suc n} {suc i} p  = fsuc (count p)

instance
  fromNat∈ : HasFromNat (Λ n)
  fromNat∈ {n} = record
    { Constraint = λ i → True (suc i ≤? n)
    ; fromNat    = λ i ⦃ i<n ⦄ → ` count (toWitness i<n)
    }
    
------------------------------------------------------------------------------
-- Decidable equality between α-equivalent terms

private
  codeΛ : (M N : Λ n) → 𝓤₀ ̇
  codeΛ (` x)   (` y)   = code x y 
  codeΛ (ƛ M)   (ƛ N)   = codeΛ M N
  codeΛ (L · M) (P · Q) = codeΛ L P × codeΛ M Q
  codeΛ (L · M) _       = ⊥
  codeΛ (` _)   _       = ⊥
  codeΛ (ƛ M)   _       = ⊥

  rΛ : (M : Λ n) → codeΛ M M
  rΛ (` x)   = r x
  rΛ (ƛ M)   = rΛ M
  rΛ (M · N) = rΛ M , rΛ N

  decodeΛ : codeΛ M N → M ≡ N
  decodeΛ {M = ` x}   {` y}   c       = cong `_   (decode c)
  decodeΛ {M = ƛ M}   {ƛ N}   c       = cong ƛ_   (decodeΛ c)
  decodeΛ {M = _ · _} {_ · _} (c , d) = cong₂ _·_ (decodeΛ c) (decodeΛ d)

instance
  CodeΛ : Code (Λ n)
  CodeΛ = record { code = codeΛ  ; r = rΛ ; decode = decodeΛ }

private
  _≟Λ_ : (M N : Λ n) → Dec (M ≡ N)
  (` x)     ≟Λ (` y) with x ≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ x=y → ¬p (decode (encode x=y))
  (ƛ M)     ≟Λ (ƛ N) with M ≟Λ N
  ... | yes p = yes (cong ƛ_ p)
  ... | no ¬p = no λ ƛM=ƛN → ¬p (decode (encode ƛM=ƛN))
  (M₁ · N₁) ≟Λ (M₂ · N₂) with M₁ ≟Λ M₂ | N₁ ≟Λ N₂
  ... | yes p | yes q = yes (decode (encode p , encode q))
  ... | yes p | no ¬q = no λ M=N → ¬q (decode (encode M=N .snd))
  ... | no ¬p | q     = no λ M=N → ¬p (decode (encode M=N .fst))
  (` _)     ≟Λ (ƛ _)    = no encode
  (` _)     ≟Λ (_ · _)  = no encode
  (ƛ _)     ≟Λ (` _)    = no encode
  (ƛ _)     ≟Λ (_ · _)  = no encode
  (_ · _)   ≟Λ (` _)    = no encode
  (_ · _)   ≟Λ (ƛ _)    = no encode

instance
  ΛisDiscrete : IsDiscrete (Λ n)
  _≟_ ⦃ ΛisDiscrete ⦄ = _≟Λ_
------------------------------------------------------------------------------
-- Variable renaming


Rename : (n m : ℕ) → 𝓤₀ ̇
Rename n m = Fin n → Fin m

ext : (Fin n → Fin m)
  → Fin (suc n) → Fin (suc m)
ext ρ fzero    = fzero
ext ρ (fsuc n) = fsuc (ρ n)

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

↑_ : Λ n
    → Λ (m + n)
↑ M = rename ρ M
  where
    ρ : Rename n (m + n)
    ρ {m = zero}  x = x
    ρ {m = suc _} x = fsuc (ρ x)

↑₁_ : Λ n → Λ (suc n)
↑₁_ = ↑_

↑₂_ : Λ n → Λ (2 + n)
↑₂_ = ↑_
------------------------------------------------------------------------------
-- Substitution

Subst : ℕ → ℕ → 𝓤₀ ̇
Subst n m = Fin n → Λ m

exts
  : Subst n m
  → Subst (suc n) (suc m)
exts σ fzero    = ` fzero
exts σ (fsuc p) = rename fsuc (σ p)

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
subst-zero N fzero    = N
subst-zero N (fsuc x) = ` x

_[_]
  : Λ (suc n) 
  → Λ n → Λ n
M [ N ] = M ⟪ subst-zero N ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 6 _-→_
data _-→_ {n : ℕ} : (M N : Λ n) → 𝓤₀ ̇ where
  β : (ƛ M) · N -→ M [ N ]

  ζ :   M -→ M′
    → ƛ M -→ ƛ M′
  ξₗ
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξᵣ
    : M -→ M′
      ---------------
    → L · M -→ L · M′

private
  code→ : {M M′ N N′ : Λ n} → (r : M -→ N) (s : M′ -→ N′) → 𝓤₀ ̇
  code→ (β {L} {M})          (β {L′} {M′})  = code L L′ × code M M′
  code→ (ζ {M} {M′} r)       (ζ {N} {N′} s) = code M N × code M′ N′ × code→ r s
  code→ (ξₗ {L₁} {L₂} {M} r) (ξₗ {L₁′} {L₂′} {M′} s) =
    code L₁ L₁′ × code L₂ L₂′ × code M M′ × code→ r s
  code→ (ξᵣ {L₁} {L₂} {M} r) (ξᵣ {L₁′} {L₂′} {M′} s) =
    code L₁ L₁′ × code L₂ L₂′ × code M M′ × code→ r s
  code→ β       _     = ⊥
  code→ (ξₗ r)  _     = ⊥
  code→ (ξᵣ r₁) _     = ⊥
  code→ (ζ r)   _     = ⊥

  toCodeΛᵣ : {M N M′ N′ : Λ n}
    → (r : M -→ N) (s : M′ -→ N′) → code→ r s → code N N′
  toCodeΛᵣ {n} (β {M} {N})    (β {M′} {N′}) (c , d)  = subst (code (M [ N ]))
    (cong₂ {x = M} {y = M′} _[_] (decode c) {N} {N′} (decode d)) (r (M [ N ]))
  toCodeΛᵣ (ζ r)  (ζ s)  (_ , d , _)     = d
  toCodeΛᵣ (ξₗ r) (ξₗ s) (_ , c , d , _) = c , d
  toCodeΛᵣ (ξᵣ r) (ξᵣ s) (_ , c , d , _) = d , c

  toCodeΛₗ : {M N M′ N′ : Λ n}
    → (r : M -→ N) (s : M′ -→ N′) → code→ r s → code M M′
  toCodeΛₗ β       β      (c , d)         = c , d
  toCodeΛₗ (ζ r)  (ζ s)   (c , _)         = c
  toCodeΛₗ (ξₗ r₁) (ξₗ s) (c , _ , d , _) = c , d
  toCodeΛₗ (ξᵣ r₁) (ξᵣ s) (c , _ , d , _) = d , c

  r→ : (r : M -→ N) → code→ r r
  r→ (β {M} {N}) = r M , r N
  r→ (ζ {M} {M′} red)      = r M , r M′ , r→ red
  r→ (ξₗ {N} {N′} {L} red) = r N , r N′ , r L , r→ red
  r→ (ξᵣ {M} {M′} {L} red) = r M , r M′ , r L , r→ red

{-
 -- TODO: Show that M -→ N is discrete
  decode→ : {M M′ N N′ : Λ n} {r : M -→ N} {s : M′ -→ N′}
    → (c : code→ r s) 
    → PathP (λ i → decode {a = M} {M′} (toCodeΛₗ r s c) i -→ decode {a = N} {N′} (toCodeΛᵣ r s c) i) r s
  decode→ {r = β} {β} (c , d) = {!!}
  decode→ {r = ζ r}  {ζ s} (c , d , e) i = ζ {!!}
  decode→ {r = ξₗ r} {ξₗ s} c = {!!}
  decode→ {r = ξᵣ r} {ξᵣ s} c = {!!}
 -} 
------------------------------------------------------------------------------
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

  code-↠ : {M N M′ N′ : Λ n}
    → (r : M -↠ N) (s : M′ -↠ N′) → 𝓤₀ ̇
  code-↠ (M ∎)          (N ∎)          = code M N
  code-↠ (_ -→⟨ r ⟩ rs) (_ -→⟨ s ⟩ ss) = code→ r s × code-↠ rs ss 
  code-↠ (_ ∎)          (_ -→⟨ _ ⟩ _) = ⊥
  code-↠ (_ -→⟨ _ ⟩ _)  (_ ∎)         = ⊥
  
open -↠-Reasoning using (_-↠_; -↠-refl; -↠-trans; -→to-↠; ·-cong; ·ₗ-cong; ·ᵣ-cong) public

trans-refl≡id : (t : M -↠ N) → -↠-trans t -↠-refl ≡ t
trans-refl≡id (_ -↠-Reasoning.∎)             = refl
trans-refl≡id (M -↠-Reasoning.-→⟨ M→N ⟩ N↠L) = 
  -↠-trans (M -↠-Reasoning.-→⟨ M→N ⟩ N↠L) -↠-refl
    ≡⟨ cong (_-↠_._-→⟨_⟩_ _ _) (trans-refl≡id N↠L) ⟩
  M -↠-Reasoning.-→⟨ M→N ⟩ N↠L ∎
  where
    open ≡-Reasoning


postulate
  -→isSet  : isSet (M -→ N)
  -↠isSet  : isSet (M -↠ N)
  ∎-isProp : isProp (M -↠ M)

