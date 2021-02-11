{-# OPTIONS --without-K --cubical #-}

module Calculus.Context where

open import Prelude

infix  3 _∈_
infixr 4 _⧺_

data Context (Ty : 𝓤 ̇) : 𝓤 ̇ where
  ∅   : Context Ty
  _,_ : (T : Ty) → (Γ : Context Ty) → Context Ty
  
private
  variable
    T   : 𝓤 ̇
    Γ Δ : Context T
    A B : T

length : Context T → ℕ
length ∅       = 0
length (A , Γ) = suc (length Γ)

lookup : (Γ : Context T) → {n : ℕ} → (p : n < length Γ) → T
lookup (A , Γ) {zero}  tt = A
lookup (A , Γ) {suc n} p  = lookup Γ p

_⧺_ : Context T → Context T → Context T
∅       ⧺ Δ = Δ
(A , Γ) ⧺ Δ = A , Γ ⧺ Δ

private
  codeCtx : {T : 𝓤 ̇} (Γ Δ : Context T) → 𝓤 ̇
  codeCtx ∅       ∅       = Unit*
  codeCtx (A , Γ) (B , Δ) = (A ≡ B) × codeCtx Γ Δ
  codeCtx _       _       = ⊥*

  rCtx : (Γ : Context T) → codeCtx Γ Γ
  rCtx ∅       = tt*
  rCtx (A , Γ) = refl , rCtx Γ

  decodeCtx : {Γ Δ : Context T} → codeCtx Γ Δ → Γ ≡ Δ
  decodeCtx {Γ = ∅}     {∅}     tt*           = refl
  decodeCtx {Γ = A , Γ} {B , Δ} (A=B , Γ=Δ) i = A=B i , decodeCtx Γ=Δ i 
  decodeCtx {Γ = ∅}     {_ , _} ()
  decodeCtx {Γ = _ , _} {∅}     ()

instance
  CodeContext : Code (Context T)
  code   ⦃ CodeContext ⦄ = codeCtx
  r      ⦃ CodeContext ⦄ = rCtx
  decode ⦃ CodeContext ⦄ = decodeCtx

_≟Cxt_ : ⦃ _ : DecEq T ⦄ → (Γ Δ : Context T) → Dec (Γ ≡ Δ)
∅       ≟Cxt ∅       = yes (decode tt*)
(A , Γ) ≟Cxt (B , Δ) with A ≟ B | Γ ≟Cxt Δ
... | yes p | yes q = yes (cong₂ _,_ p q)
... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
... | no ¬p | _     = no λ eq → ¬p (encode eq .fst)
∅       ≟Cxt (B , Δ) = no λ p → ⊥*-elim (encode p)
(A , Γ) ≟Cxt ∅       = no λ p → ⊥*-elim (encode p)

instance
  DecEqCxt : ⦃ _ : DecEq T ⦄ → DecEq (Context T)
  _≟_ ⦃ DecEqCxt ⦄ = _≟Cxt_

------------------------------------------------------------------------------
-- Membership

data _∈_ {T : 𝓤 ̇} : T → Context T → 𝓤 ̇ where
  Z     : (B=A : B ≡ A) → A ∈ B , Γ
  S_    : (A∈Γ : A ∈ Γ) → A ∈ B , Γ
  
count : (Γ : Context T) → {n : ℕ} → (p : n < length Γ) → lookup Γ p ∈ Γ
count (_ , _) {zero}    tt = Z refl
count (_ , Γ) {(suc n)} p  = S count Γ p

ext
  : (∀ {A : T} →       A ∈ Γ →     A ∈ Δ)
    ------------------------------------------
  → (∀ {A B : T} → A ∈ B , Γ → A ∈ B , Δ)
ext ρ (Z p) =  Z p
ext ρ (S x) =  S (ρ x)

Rename : {T : 𝓤 ̇} → Context T → Context T → 𝓤 ̇ 
Rename {T = T} Γ Δ = {A : T} → A ∈ Γ → A ∈ Δ

private
  code∈ : {A : T} (x y : A ∈ Γ) → universe-of T ̇
  code∈ (Z p) (Z q) = p ≡ q -- p ≡ q
  code∈ (S x) (S y) = code∈ x y
  code∈ _     _     = ⊥*

  r∈ : (x : A ∈ Γ) → code∈ x x
  r∈ (Z _) = refl
  r∈ (S x) = r∈ x

  decode∈ : {x y : A ∈ Γ} → code∈ x y → x ≡ y
  decode∈ {x = Z p} {Z q} c = cong Z c  
  decode∈ {x = S x} {S y} c = cong S_ (decode∈ c)

instance
  Code∈ : Code (A ∈ Γ)
  Code∈ = record { code = code∈ ; r = r∈ ; decode = decode∈ }

_≟∈_ : ⦃ DecEq T ⦄ → {A : T}
  → (x y : A ∈ Γ) → Dec (x ≡ y)
Z p   ≟∈ Z q = yes (cong Z (≟→isSet _ _ p q ))
(S x) ≟∈ (S y) with x ≟∈ y
... | yes p = yes (cong S_ p)
... | no ¬p = no λ eq → ¬p (decode (encode eq))
(S _) ≟∈ Z _   = no λ eq → ⊥*-elim (encode eq)
Z _   ≟∈ (S _) = no λ eq → ⊥*-elim (encode eq)

instance
  DecEq∈ : ⦃ DecEq T ⦄ → {A : T} {Γ : Context T} → DecEq (A ∈ Γ)
  _≟_ ⦃ DecEq∈ ⦄ = _≟∈_
