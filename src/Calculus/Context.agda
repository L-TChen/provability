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
    Γ Δ   : Context Ty
    A B   : Ty
    
module CxtEncodeDecode {Ty : 𝓤 ̇} where
  code : (Γ Δ : Context Ty) → 𝓤 ̇
  code ∅       ∅       = Unit*
  code (Γ , A) (Δ , B) = code Γ Δ × (A ≡ B)
  code ∅       (_ , _) = ⊥*
  code (_ , _) ∅       = ⊥*

  r : (Γ : Context Ty) → code Γ Γ
  r ∅       = tt*
  r (Γ , A) = r Γ , refl

  encode : A ≡ B → code A B
  encode {A = A} A=B = transport (cong (code A) A=B) (r A)
  
  decode : {Γ Δ : Context Ty} → code Γ Δ → Γ ≡ Δ
  decode {Γ = ∅}     {∅}     tt*  = refl
  decode {Γ = Γ , A} {Δ , B} (Γ=Δ , A=B) i = decode Γ=Δ i , A=B i
  decode {Γ = ∅}     {_ , _} ()
  decode {Γ = _ , _} {∅}     ()

  module _ ⦃ _ : DecEq Ty ⦄ where
    _≟Cxt_ : (Γ Δ : Context Ty) → Dec (Γ ≡ Δ)
    ∅       ≟Cxt ∅       = yes (decode tt*)
    (Γ , A) ≟Cxt (Δ , B) with Γ ≟Cxt Δ | A ≟ B
    ... | yes p | yes q = yes (cong₂ _,_ p q)
    ... | yes p | no ¬q = no λ p → ¬q (encode p .snd)
    ... | no ¬p | q     = no λ p → ¬p (decode (encode p .fst))
    ∅       ≟Cxt (Δ , B) = no λ p → ⊥*-elim (encode p)
    (Γ , A) ≟Cxt ∅       = no λ p → ⊥*-elim (encode p)

    instance
      DecEqCxt : DecEq (Context Ty)
      _≟_ ⦃ DecEqCxt ⦄ = _≟Cxt_
open CxtEncodeDecode using (DecEqCxt) public

------------------------------------------------------------------------------
-- Membership

data _∋_ {Ty : 𝓤 ̇} : Context Ty → Ty → 𝓤 ̇ where
  Z  :             Γ , A ∋ A
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

module ∋EncodeDecode {Ty : 𝓤 ̇} where
  code : (x y : Γ ∋ A) → 𝓤 ̇
  code Z = codeZ
    where
      codeZ : (y : Γ ∋ A) → 𝓤 ̇
      codeZ Z     = Unit*
      codeZ (S y) = ⊥*
  code (S x) Z     = ⊥*
  code (S x) (S y) = code x y

  r : (x : Γ ∋ A) → code x x
  r Z     = tt*
  r (S x) = r x

  encode : {x y : Γ ∋ A} → x ≡ y → code x y
  encode {x = x} x=y = transport (cong (code x) x=y) (r x)

  postulate
    decode : {x y : _∋_ {𝓤} {Ty} Γ A} → code x y → x ≡ y
