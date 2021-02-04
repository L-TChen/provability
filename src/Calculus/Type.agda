{-# OPTIONS --without-K --cubical #-}

module Calculus.Type where

open import Prelude

infixr 7 _→̇_
infixr 8 _×̇_

data 𝕋 : Set where
  nat  : 𝕋
  ⊤̇    : 𝕋
  _×̇_  : 𝕋 → 𝕋 → 𝕋
  _→̇_  : 𝕋 → 𝕋 → 𝕋

private
  variable
    A B C D A′ B′ C′ : 𝕋

  code : (A B : 𝕋) → 𝓤₀ ̇
  code ⊤̇       ⊤̇       = Unit
  code nat     nat       = Unit
  code (A ×̇ B) (C ×̇ D) = code A C × code B D
  code (A →̇ B) (C →̇ D) = code A C × code B D
  code nat     (_ ×̇ _) = ⊥
  code nat     (_ →̇ _) = ⊥
  code (_ ×̇ _) nat     = ⊥
  code (_ ×̇ _) (_ →̇ _) = ⊥
  code (_ →̇ _) nat     = ⊥
  code (_ →̇ _) (_ ×̇ _) = ⊥
  code nat     ⊤̇       = ⊥ 
  code ⊤̇       nat     = ⊥
  code ⊤̇       (A ×̇ B) = ⊥
  code ⊤̇       (A →̇ B) = ⊥
  code (A ×̇ B) ⊤̇       = ⊥
  code (A →̇ B) ⊤̇       = ⊥


  r : (A : 𝕋) → code A A
  r nat     = tt
  r ⊤̇       = tt
  r (A ×̇ B) = r A , r B
  r (A →̇ B) = r A , r B

  encode : A ≡ B → code A B
  encode {A = A} A=B = transport (cong (code A) A=B) (r A)

  decode : {A B : 𝕋} → code A B → A ≡ B
  decode {A = ⊤̇}     {B = ⊤̇}     tt        = refl
  decode {A = nat}   {B = nat}   tt        = refl
  decode {A = A ×̇ B} {B = C ×̇ D} (p , q) i = decode p i ×̇ decode q i
  decode {A = A →̇ B} {B = C →̇ D} (p , q) i = decode p i →̇ decode q i

  _≟Tp_ : (A B : 𝕋) → Dec (A ≡ B)
  ⊤̇ ≟Tp ⊤̇             = yes (decode tt)
  nat ≟Tp nat         = yes (decode tt)
  (A ×̇ B) ≟Tp (C ×̇ D) with A ≟Tp C | B ≟Tp D
  ... | yes p | yes q = yes (cong₂ _×̇_ p q)
  ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
  ... | no ¬p | _     = no λ eq → ¬p (decode (encode eq .fst))
  (A →̇ B) ≟Tp (C →̇ D) with A ≟Tp C | B ≟Tp D
  ... | yes p | yes q = yes (cong₂ _→̇_ p q)
  ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
  ... | no ¬p | _     = no λ eq → ¬p (decode (encode eq .fst))
  nat     ≟Tp (_ ×̇ _) = no encode 
  nat     ≟Tp (_ →̇ _) = no encode
  (A ×̇ B) ≟Tp nat     = no encode
  (A ×̇ B) ≟Tp (C →̇ D) = no encode
  (A →̇ B) ≟Tp nat     = no encode
  (A →̇ B) ≟Tp (C ×̇ D) = no encode
  nat       ≟Tp ⊤̇     = no encode
  ⊤̇       ≟Tp nat     = no encode
  ⊤̇       ≟Tp (A ×̇ B) = no encode
  ⊤̇       ≟Tp (A →̇ B) = no encode
  (A ×̇ B) ≟Tp ⊤̇       = no encode
  (A →̇ B) ≟Tp ⊤̇       = no encode

instance
  DecEq𝕋 : DecEq 𝕋 
  _≟_ ⦃ DecEq𝕋 ⦄ = _≟Tp_

dom≡ : A →̇ B ≡ A′ →̇ B′ → A ≡ A′
dom≡ p = decode (encode p .fst)

-- rng≡ : A →̇ B ≡ A′ →̇ B′ → B ≡ B′
-- rng≡ eq = decode (encode eq .snd)

-- ×ₗ≡ : A ×̇ B ≡ A′ ×̇ B′ → A ≡ A′ 
-- ×ₗ≡ eq = decode (encode eq .fst)

-- ×ᵣ≡ : A ×̇ B ≡ A′ ×̇ B′ → B ≡ B′ 
-- ×ᵣ≡ eq = decode (encode eq .snd)

-- ℕ≢→ : ¬ nat ≡ A →̇ B
-- ℕ≢→ = encode

-- ℕ≢× : ¬ nat ≡ A ×̇ B
-- ℕ≢× = encode

-- ×≢→ : ¬ A ×̇ B ≡ C →̇ D
-- ×≢→ = encode
