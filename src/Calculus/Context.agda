{-# OPTIONS --without-K --cubical #-}

module Calculus.Context where

open import Prelude

infix  3 _∈_

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

module CxtEncodeDecode {T : 𝓤 ̇} where
  code : (Γ Δ : Context T) → 𝓤 ̇
  code ∅       ∅       = Unit*
  code (A , Γ) (B , Δ) = (A ≡ B) × code Γ Δ
  code ∅       (_ , _) = ⊥*
  code (_ , _) ∅       = ⊥*

  r : (Γ : Context T) → code Γ Γ
  r ∅       = tt*
  r (A , Γ) = refl , r Γ

  encode : A ≡ B → code A B
  encode {A = A} A=B = transport (cong (code A) A=B) (r A)
  
  decode : {Γ Δ : Context T} → code Γ Δ → Γ ≡ Δ
  decode {∅}     {∅}     tt*           = refl
  decode {A , Γ} {B , Δ} (A=B , Γ=Δ) i = A=B i , decode Γ=Δ i 
  decode {∅}     {_ , _} ()
  decode {_ , _} {∅}     ()

  module _ ⦃ _ : DecEq T ⦄ where
    _≟Cxt_ : (Γ Δ : Context T) → Dec (Γ ≡ Δ)
    ∅       ≟Cxt ∅       = yes (decode tt*)
    (A , Γ) ≟Cxt (B , Δ) with A ≟ B | Γ ≟Cxt Δ
    ... | yes p | yes q = yes (cong₂ _,_ p q)
    ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
    ... | no ¬p | _     = no λ eq → ¬p (encode eq .fst)
    ∅       ≟Cxt (B , Δ) = no λ p → ⊥*-elim (encode p)
    (A , Γ) ≟Cxt ∅       = no λ p → ⊥*-elim (encode p)

    instance
      DecEqCxt : DecEq (Context T)
      _≟_ ⦃ DecEqCxt ⦄ = _≟Cxt_
open CxtEncodeDecode using (DecEqCxt) public

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
ext ρ (Z p)  =  Z p
ext ρ (S x)  =  S (ρ x)

Rename : {T : 𝓤 ̇} → Context T → Context T → 𝓤 ̇ 
Rename {T = T} Γ Δ = {A : T} → A ∈ Γ → A ∈ Δ

module ∈EncodeDecode where
  code : {T : 𝓤 ̇} {A : T} {Γ : Context T} (x y : A ∈ Γ) → 𝓤 ̇
  code (Z p) (Z q) = p ≡ q
  code (S x) (S y) = code x y
  code (Z _) (S _) = ⊥*
  code (S _) (Z _) = ⊥*

  r : (x : A ∈ Γ) → code x x
  r (Z _) = refl
  r (S x)   = r x

  encode : {x y : A ∈ Γ} → x ≡ y → code x y
  encode {x = x} x=y = transport (cong (code x) x=y) (r x)

  decode : {x y : A ∈ Γ} → code x y → x ≡ y
  decode {x = Z p} {Z q} c = cong Z c  
  decode {x = S x} {S y} c = cong S_ (decode c)

  module _ ⦃ decEqT : DecEq T ⦄ where
    _≟∈_ : {A : T} (x y : A ∈ Γ) → Dec (x ≡ y)
    Z p   ≟∈ Z q = yes (cong Z (≟→isSet _ _ p q ))
    (S x) ≟∈ (S y) with x ≟∈ y
    ... | yes p = yes (cong S_ p)
    ... | no ¬p = no λ eq → ¬p (decode (encode eq))
    (S _) ≟∈ Z _   = no λ eq → ⊥*-elim (encode eq)
    Z _   ≟∈ (S _) = no λ eq → ⊥*-elim (encode eq)

    instance
      DecEq∈ : {A : T} {Γ : Context T} → DecEq (A ∈ Γ)
      _≟_ ⦃ DecEq∈ ⦄ = _≟∈_
