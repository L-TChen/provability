{-# OPTIONS --without-K --cubical #-}

module Calculus.Type where

open import Prelude

infixr 7 _→̇_
infixr 8 _×̇_

data 𝕋 : Set where
  ℕ̇    : 𝕋
  ⊤̇    : 𝕋
  _×̇_  : 𝕋 → 𝕋 → 𝕋
  _→̇_  : 𝕋 → 𝕋 → 𝕋

private
  variable
    A B C D A′ B′ C′ : 𝕋

  code : (A B : 𝕋) → 𝓤₀ ̇
  code ⊤̇       ⊤̇       = Unit
  code ℕ̇       ℕ̇       = Unit
  code (A ×̇ B) (C ×̇ D) = code A C × code B D
  code (A →̇ B) (C →̇ D) = code A C × code B D
  code ℕ̇       (_ ×̇ _) = ⊥
  code ℕ̇       (_ →̇ _) = ⊥
  code (_ ×̇ _) ℕ̇       = ⊥
  code (_ ×̇ _) (_ →̇ _) = ⊥
  code (_ →̇ _) ℕ̇       = ⊥
  code (_ →̇ _) (_ ×̇ _) = ⊥
  code ℕ̇       ⊤̇       = ⊥ 
  code ⊤̇       ℕ̇       = ⊥
  code ⊤̇       (A ×̇ B) = ⊥
  code ⊤̇       (A →̇ B) = ⊥
  code (A ×̇ B) ⊤̇       = ⊥
  code (A →̇ B) ⊤̇       = ⊥


  r : (A : 𝕋) → code A A
  r ℕ̇       = tt
  r ⊤̇       = tt
  r (A ×̇ B) = r A , r B
  r (A →̇ B) = r A , r B

  encode : A ≡ B → code A B
  encode {A = A} A=B = transport (cong (code A) A=B) (r A)

  decode : {A B : 𝕋} → code A B → A ≡ B
  decode {A = ⊤̇}     {B = ⊤̇}     tt        = refl
  decode {A = ℕ̇}     {B = ℕ̇}     tt        = refl
  decode {A = A ×̇ B} {B = C ×̇ D} (p , q) i = decode p i ×̇ decode q i
  decode {A = A →̇ B} {B = C →̇ D} (p , q) i = decode p i →̇ decode q i

  _≟Tp_ : (A B : 𝕋) → Dec (A ≡ B)
  ⊤̇ ≟Tp ⊤̇             = yes (decode tt)
  ℕ̇ ≟Tp ℕ̇             = yes (decode tt)
  (A ×̇ B) ≟Tp (C ×̇ D) with A ≟Tp C | B ≟Tp D
  ... | yes p | yes q = yes (cong₂ _×̇_ p q)
  ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
  ... | no ¬p | _     = no λ eq → ¬p (decode (encode eq .fst))
  (A →̇ B) ≟Tp (C →̇ D) with A ≟Tp C | B ≟Tp D
  ... | yes p | yes q = yes (cong₂ _→̇_ p q)
  ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
  ... | no ¬p | _     = no λ eq → ¬p (decode (encode eq .fst))
  ℕ̇       ≟Tp (_ ×̇ _) = no encode 
  ℕ̇       ≟Tp (_ →̇ _) = no encode
  (A ×̇ B) ≟Tp ℕ̇       = no encode
  (A ×̇ B) ≟Tp (C →̇ D) = no encode
  (A →̇ B) ≟Tp ℕ̇       = no encode
  (A →̇ B) ≟Tp (C ×̇ D) = no encode
  ℕ̇       ≟Tp ⊤̇       = no encode
  ⊤̇       ≟Tp ℕ̇       = no encode
  ⊤̇       ≟Tp (A ×̇ B) = no encode
  ⊤̇       ≟Tp (A →̇ B) = no encode
  (A ×̇ B) ≟Tp ⊤̇       = no encode
  (A →̇ B) ≟Tp ⊤̇       = no encode

instance
  DecEq𝕋 : DecEq 𝕋 
  _≟_ ⦃ DecEq𝕋 ⦄ = _≟Tp_

dom≡ : A →̇ B ≡ A′ →̇ B′ → A ≡ A′
dom≡ eq = decode (encode eq .fst)

rng≡ : A →̇ B ≡ A′ →̇ B′ → B ≡ B′
rng≡ eq = decode (encode eq .snd)

×ₗ≡ : A ×̇ B ≡ A′ ×̇ B′ → A ≡ A′ 
×ₗ≡ eq = decode (encode eq .fst)

×ᵣ≡ : A ×̇ B ≡ A′ ×̇ B′ → B ≡ B′ 
×ᵣ≡ eq = decode (encode eq .snd)

ℕ≢→ : ¬ ℕ̇ ≡ A →̇ B
ℕ≢→ = encode

ℕ≢× : ¬ ℕ̇ ≡ A ×̇ B
ℕ≢× = encode

×≢→ : ¬ A ×̇ B ≡ C →̇ D
×≢→ = encode
