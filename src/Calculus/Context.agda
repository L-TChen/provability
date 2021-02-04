{-# OPTIONS --without-K --cubical #-}

module Calculus.Context where

open import Prelude

infix  3 _∋_
infixl 4  _,_ 

data Context (Ty : 𝓤 ̇) : 𝓤 ̇ where
  ∅   : Context Ty
  _,_ : (Γ : Context Ty) → (T : Ty) → Context Ty
  
private
  variable
    Ty    : 𝓤 ̇
    Γ Δ Θ : Context Ty
    A B C : Ty

------------------------------------------------------------------------------
-- Membership

data _∋_ {Ty : 𝓤 ̇} : Context Ty → Ty → 𝓤 ̇ where
  Z  : Γ , A ∋ A
  S_ : Γ     ∋ A → Γ , B ∋ A

length : Context Ty → ℕ
length ∅       = 0
length (Γ , A) = suc (length Γ)

lookup : (Γ : Context Ty) → {n : ℕ} → (p : n < length Γ) → Ty
lookup (Γ , A) {zero} tt = A
lookup (Γ , A) {suc n} p = lookup Γ p

count : (Γ : Context Ty) → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup Γ p
count (_ , _) {zero}    tt = Z
count (Γ , _) {(suc n)} p  = S count Γ p

ext
  : (∀ {A : Ty} →       Γ ∋ A →     Δ ∋ A)
    ------------------------------------------
  → (∀ {A B : Ty} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

Rename : {Ty : 𝓤 ̇} → Context Ty → Context Ty → 𝓤 ̇
Rename Γ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A

module DecidableEquality
  {𝕋       : 𝓤 ̇}
  (code𝕋   : 𝕋 → 𝕋 → 𝓤₀ ̇)
  (decode𝕋 : {A B : 𝕋} → code𝕋 A B → A ≡ B)
  (r𝕋      : (A : 𝕋) → code𝕋 A A)
  (encode𝕋 : {A B : 𝕋} → A ≡ B → code𝕋 A B)
  (_≟𝕋_    : (A B : 𝕋) → Dec (A ≡ B))
  where 

  private
    Cxt = Context 𝕋

  code : (Γ Δ : Cxt) → 𝓤₀ ̇
  code ∅       ∅       = Unit
  code (Γ , A) (Δ , B) = code Γ Δ × code𝕋 A B
  code ∅       (_ , _) = ⊥
  code (_ , _) ∅       = ⊥

  r : (Γ : Cxt) → code Γ Γ
  r ∅       = tt
  r (Γ , A) = r Γ , r𝕋 A 

  encode : A ≡ B → code A B
  encode {A = A} A=B = transport (cong (code A) A=B) (r A)
  
  decode : {Γ Δ : Cxt} → code Γ Δ → Γ ≡ Δ
  decode {∅}     {∅}     tt   = refl
  decode {Γ , A} {Δ , B} p  i = decode (fst p) i , decode𝕋 (snd p) i
  decode {∅}     {_ , _} ()
  decode {_ , _} {∅}     ()

  _≟Cxt_ : (Γ Δ : Cxt) → Dec (Γ ≡ Δ)
  ∅       ≟Cxt ∅       = yes (decode tt)
  (Γ , A) ≟Cxt (Δ , B) with Γ ≟Cxt Δ | A ≟𝕋 B
  ... | yes p | yes q = yes (cong₂ _,_ p q)
  ... | yes p | no ¬q = no λ Γ=Δ → ¬q (decode𝕋 (encode Γ=Δ .snd))
  ... | no ¬p | q     = no λ Γ=Δ → ¬p (decode (encode Γ=Δ .fst))
  ∅       ≟Cxt (Δ , B) = no encode
  (Γ , T) ≟Cxt ∅       = no encode

  instance
    DecEqCxt : DecEq Cxt
    _≟_ ⦃ DecEqCxt ⦄ = _≟Cxt_
open DecidableEquality using (DecEqCxt)
 
