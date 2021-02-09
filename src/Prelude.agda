{-# OPTIONS --without-K --cubical #-}

module Prelude where

open import Agda.Builtin.FromNat                 public
  renaming (Number to HasFromNat)

open import Cubical.Foundations.Everything       public
  hiding (id; ℓ-max; _≡⟨_⟩_; _∎; ≡⟨⟩-syntax; ⋆)
open import Cubical.Relation.Nullary             public
  hiding (⟪_⟫)
open import Cubical.HITs.PropositionalTruncation public
  hiding (map)
  renaming (elim to truncElim)

open import Cubical.Data.Sigma                     public
open import Cubical.Data.Unit                      public
open import Cubical.Data.Empty                     public
  renaming (rec to ⊥rec; elim to ⊥-elim)
open import Cubical.Data.Bool                      public
  hiding (_≟_)
open import Cubical.Data.Nat                       public
  using (ℕ; zero; suc; _+_; _∸_; fromNatℕ)
open import Cubical.Data.Nat.Order.Recursive as ℕₚ public
  using (_≤_; _<_)

open import Universes public
open import Later     public

private
  variable
    A B C : 𝓤 ̇
    n m   : ℕ

infixr -1 Π Σ′ ∃′ _➝_

infix 4 _≢_
_≢_ : {A : 𝓤 ̇} → A → A → 𝓤 ̇
x ≢ y = x ≡ y → ⊥

∥_∥* : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
∥_∥* {𝓥 = 𝓥} X = Lift {j = 𝓥} ∥ X ∥

⊥*-elim : ⊥* {𝓤} → A
⊥*-elim ()

pattern ∣_∣* x = lift (∣_∣ x)

------------------------------------------------------------------------
-- Π x ꞉ A , Σ a ꞉ A , ∃ a ꞉ A notation in Type Theory

syntax Π  {A = A} (λ x → b) = Π[ x ꞉ A ] b
syntax Σ′ {A = A} (λ x → b) = Σ[ x ꞉ A ] b
syntax ∃′ {A = A} (λ x → b) = ∃[ x ꞉ A ] b

Π : (B : A → 𝓥 ̇) → (universe-of A) ⊔ 𝓥 ̇
Π {A = A} B = (x : A) → B x

Σ′ : (B : A → 𝓥 ̇) → (universe-of A) ⊔ 𝓥 ̇
Σ′ {A = A} B = Σ A B

∃′ : (B : A → 𝓥 ̇) → (universe-of A) ⊔ 𝓥 ̇
∃′ {A = A} B = ∥ Σ A B ∥

_➝_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ➝ B = A → B

------------------------------------------------------------------------------
-- Some properties about relation

_respects_on-the-left : {A : 𝓤 ̇} {B : 𝓥 ̇}
  → (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → (_∼_ : A → A → 𝓤 ̇) → 𝓤 ⊔ 𝓥 ̇
_respects_on-the-left {𝓤} {𝓥} {A} {B} _≈_ _∼_ = {x x′ : A} {y : B} → x ∼ x′ → x′ ≈ y → x ≈ y

IsRightTotal : {A : 𝓤 ̇} {B : 𝓥 ̇} (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
IsRightTotal {𝓤} {𝓥} {A} {B} _≈_ = (y : B) → ∃[ x ꞉ A ] (x ≈ y)

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id x = x

module ≡-Reasoning where
  open import Cubical.Foundations.Prelude public
    using (_≡⟨_⟩_; ≡⟨⟩-syntax; _∎)

  infix  1 begin_
  infixr 2 _≡⟨⟩_
  
  begin_ : {x y : A} (r : x ≡ y) → x ≡ y
  begin x=y = x=y

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes tt
suc m ≤? zero  = no λ ()
suc m ≤? suc n = m ≤? n

record DecEq (A : 𝓤 ̇) : 𝓤 ̇ where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

open DecEq ⦃ ... ⦄ public

instance
  DecEqUnit : DecEq Unit
  DecEqUnit = record { _≟_ = λ {tt tt → yes refl} }

  DecEqBool : DecEq Bool
  _≟_ ⦃ DecEqBool ⦄ = Cubical.Data.Bool._≟_
  
--  DecEqℕ : DecEq ℕ
--  _≟_ ⦃ DecEqℕ ⦄ x y with x ℕₚ.≟ y
--  ... | ℕₚ.eq x=y = yes x=y
--  ... | ℕₚ.lt x<y = no (ℕₚ.<→≢ x<y)
--  ... | ℕₚ.gt x>y = no λ x=y → ℕₚ.<→≢ x>y (sym x=y)
