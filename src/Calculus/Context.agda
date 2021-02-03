{-# OPTIONS --without-K --cubical #-}

module Calculus.Context where

open import Cubical.Data.Nat.Order.Recursive

open import Prelude
open import Calculus.Type

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
