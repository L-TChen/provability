{-# OPTIONS --without-K --cubical #-}

module Calculus.SystemT.Type where

open import Prelude

infixr 7 _`→_
infixr 8 _`×_

data 𝕋 : 𝓤₀ ̇ where
  nat   : 𝕋
  `⊤    : 𝕋
  `⊥    : 𝕋
  _`×_  : 𝕋 → 𝕋 → 𝕋
  _`→_  : 𝕋 → 𝕋 → 𝕋

private
  variable
    A B C D : 𝕋


module EncodeDecode where
  code : (A B : 𝕋) → 𝓤₀ ̇
  code `⊤       `⊤       = Unit
  code `⊥       `⊥       = Unit
  code nat      nat      = Unit
  code (A `× B) (C `× D) = code A C × code B D
  code (A `→ B) (C `→ D) = code A C × code B D
  code `⊤       _        = ⊥
  code `⊥       _        = ⊥
  code nat      _        = ⊥
  code (_ `× _) _        = ⊥
  code (_ `→ _) _        = ⊥

  r : (A : 𝕋) → code A A
  r nat      = tt
  r `⊤       = tt
  r `⊥       = tt
  r (A `× B) = r A , r B
  r (A `→ B) = r A , r B

  encode : A ≡ B → code A B
  encode A=B = transport (cong (code _) A=B) (r _)

  decode : {A B : 𝕋} → code A B → A ≡ B
  decode {A = `⊤}     {B = `⊤}     tt        = refl
  decode {A = `⊥}     {B = `⊥}     tt        = refl
  decode {A = nat}    {B = nat }   tt        = refl
  decode {A = A `× B} {B = C `× D} (p , q) i = decode p i `× decode q i
  decode {A = A `→ B} {B = C `→ D} (p , q) i = decode p i `→ decode q i

  _≟Tp_ : (A B : 𝕋) → Dec (A ≡ B)
  `⊤ ≟Tp `⊤           = yes (decode tt)
  `⊥ ≟Tp `⊥           = yes (decode tt)
  nat ≟Tp nat         = yes (decode tt)
  (A `× B) ≟Tp (C `× D) with A ≟Tp C | B ≟Tp D
  ... | yes p | yes q = yes (cong₂ _`×_ p q)
  ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
  ... | no ¬p | _     = no λ eq → ¬p (decode (encode eq .fst))
  (A `→ B) ≟Tp (C `→ D) with A ≟Tp C | B ≟Tp D
  ... | yes p | yes q = yes (cong₂ _`→_ p q)
  ... | yes p | no ¬q = no λ eq → ¬q (decode (encode eq .snd))
  ... | no ¬p | _     = no λ eq → ¬p (decode (encode eq .fst))
  `⊤       ≟Tp `⊥       = no encode
  `⊤       ≟Tp nat      = no encode
  `⊤       ≟Tp (A `× B) = no encode
  `⊤       ≟Tp (A `→ B) = no encode
  `⊥       ≟Tp `⊤       = no encode
  `⊥       ≟Tp nat      = no encode
  `⊥       ≟Tp (A `× B) = no encode
  `⊥       ≟Tp (A `→ B) = no encode
  nat      ≟Tp `⊤       = no encode
  nat      ≟Tp `⊥       = no encode
  nat      ≟Tp (_ `× _) = no encode 
  nat      ≟Tp (_ `→ _) = no encode
  (A `× B) ≟Tp `⊤       = no encode
  (A `× B) ≟Tp `⊥       = no encode
  (A `× B) ≟Tp nat      = no encode
  (A `× B) ≟Tp (C `→ D) = no encode
  (A `→ B) ≟Tp `⊤       = no encode
  (A `→ B) ≟Tp `⊥       = no encode
  (A `→ B) ≟Tp nat      = no encode
  (A `→ B) ≟Tp (C `× D) = no encode

  instance
    DecEq𝕋 : DecEq 𝕋 
    _≟_ ⦃ DecEq𝕋 ⦄ = _≟Tp_
open EncodeDecode using (DecEq𝕋) public
open EncodeDecode

dom≡ : A `→ B ≡ C `→ D → A ≡ C
dom≡ p = decode (encode p .fst)

rng≡ : A `→ B ≡ C `→ D → B ≡ D
rng≡ p = decode (encode p .snd)

×ₗ≡ : A `× B ≡ C `× D → A ≡ C
×ₗ≡ p = decode (encode p .fst)

×ᵣ≡ : A `× B ≡ C `× D → B ≡ D
×ᵣ≡ p = decode (encode p .snd)

ℕ≢→ : ¬ nat ≡ A `→ B
ℕ≢→ = encode

ℕ≢× : ¬ nat ≡ A `× B
ℕ≢× = encode

×≢→ : ¬ A `× B ≡ C `→ D
×≢→ = encode
