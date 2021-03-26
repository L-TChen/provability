{-# OPTIONS --without-K --cubical --no-import-sorts #-}

module Prelude.Notations where

open import Cubical.Core.Everything       
open import Cubical.Data.Empty
  using (⊥)
open import Cubical.HITs.PropositionalTruncation 

open import Prelude.Universes public

private
  variable
    A B C : 𝓤 ̇

infix  4  _≢_
infixr -1 _➝_
infixr -2 Π Σ′ ∃′ 

_≢_ : {A : 𝓤 ̇} → A → A → 𝓤 ̇
x ≢ y = x ≡ y → ⊥

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
