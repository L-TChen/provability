{-# OPTIONS --without-K --cubical #-}

module Calculus.Context where

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

lookup : Context Ty → ℕ → Ty
lookup Γ n = {!!}

count : (n : ℕ) → Γ ∋ lookup Γ n
count n = {!!}

ext
  : (∀ {A : Ty} →       Γ ∋ A →     Δ ∋ A)
    ------------------------------------------
  → (∀ {A B : Ty} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

Rename : {Ty : 𝓤 ̇} → Context Ty → Context Ty → 𝓤 ̇
Rename Γ Γ′ = ∀ {A} → Γ ∋ A → Γ′ ∋ A
