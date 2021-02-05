{-# OPTIONS --without-K --cubical #-}

module Calculus.Context where

open import Prelude

infix  3 _∈_

data Context (Ty : 𝓤 ̇) : 𝓤 ̇ where
  ∅   : Context Ty
  _,_ : (T : Ty) → (Γ : Context Ty) → Context Ty
  
private
  variable
    Ty    : 𝓤 ̇
    Γ Δ   : Context Ty
    A B   : Ty
    
module CxtEncodeDecode {Ty : 𝓤 ̇} where
  code : (Γ Δ : Context Ty) → 𝓤 ̇
  code ∅       ∅       = Unit*
  code (A , Γ) (B , Δ) = (A ≡ B) × code Γ Δ
  code ∅       (_ , _) = ⊥*
  code (_ , _) ∅       = ⊥*

  r : (Γ : Context Ty) → code Γ Γ
  r ∅       = tt*
  r (A , Γ) = refl , r Γ

  encode : A ≡ B → code A B
  encode {A = A} A=B = transport (cong (code A) A=B) (r A)
  
  decode : {Γ Δ : Context Ty} → code Γ Δ → Γ ≡ Δ
  decode {Γ = ∅}     {∅}     tt*  = refl
  decode {Γ = A , Γ} {B , Δ} (A=B , Γ=Δ) i = A=B i , decode Γ=Δ i 
  decode {Γ = ∅}     {_ , _} ()
  decode {Γ = _ , _} {∅}     ()

  module _ ⦃ _ : DecEq Ty ⦄ where
    _≟Cxt_ : (Γ Δ : Context Ty) → Dec (Γ ≡ Δ)
    ∅       ≟Cxt ∅       = yes (decode tt*)
    (A , Γ) ≟Cxt (B , Δ) with A ≟ B | Γ ≟Cxt Δ
    ... | yes p | yes q = yes (cong₂ _,_ p q)
    ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
    ... | no ¬p | _     = no λ eq → ¬p (encode eq .fst)
    ∅       ≟Cxt (B , Δ) = no λ p → ⊥*-elim (encode p)
    (A , Γ) ≟Cxt ∅       = no λ p → ⊥*-elim (encode p)

    instance
      DecEqCxt : DecEq (Context Ty)
      _≟_ ⦃ DecEqCxt ⦄ = _≟Cxt_
open CxtEncodeDecode using (DecEqCxt) public

------------------------------------------------------------------------------
-- Membership

data _∈_ {Ty : 𝓤 ̇} : Ty → Context Ty → 𝓤 ̇ where
  Z  :         A ∈ A , Γ
  S_ : A ∈ Γ → A ∈ B , Γ

length : Context Ty → ℕ
length ∅       = 0
length (A , Γ) = suc (length Γ)

lookup : (Γ : Context Ty) → {n : ℕ} → (p : n < length Γ) → Ty
lookup (A , Γ) {zero} tt = A
lookup (A , Γ) {suc n} p = lookup Γ p

count : (Γ : Context Ty) → {n : ℕ} → (p : n < length Γ) → lookup Γ p ∈ Γ
count (_ , _) {zero}    tt = Z
count (_ , Γ) {(suc n)} p  = S count Γ p

ext
  : (∀ {A : Ty} →       A ∈ Γ →     A ∈ Δ)
    ------------------------------------------
  → (∀ {A B : Ty} → A ∈ B , Γ → A ∈ B , Δ)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

Rename : {Ty : 𝓤 ̇} → Context Ty → Context Ty → 𝓤 ̇
Rename Γ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

module ∈EncodeDecode {Ty : 𝓤 ̇} where
  code : (x y : A ∈ Γ) → 𝓤 ̇
  code Z = codeZ
    where
      codeZ : (y : A ∈ Γ) → 𝓤 ̇
      codeZ Z     = Unit*
      codeZ (S y) = ⊥*
  code (S x) Z     = ⊥*
  code (S x) (S y) = code x y

  r : (x : A ∈ Γ) → code x x
  r Z     = tt*
  r (S x) = r x

  encode : {x y : A ∈ Γ} → x ≡ y → code x y
  encode {x = x} x=y = transport (cong (code x) x=y) (r x)

  postulate
    decode : {x y : _∈_ {𝓤} {Ty} A Γ} → code x y → x ≡ y
