{-# OPTIONS --without-K --cubical #-}

module Function.Partial.Properties where

open import Cubical.Functions.Logic
  using (⇒∶_⇐∶_; ⇐∶_⇒∶_)
open import Cubical.Functions.Embedding

open import Prelude
open import Function.Partial.Base

private
  variable
    A B : 𝓤 ̇
    
{-
η-is-embedding : isEmbedding (η {𝓤} {A} 𝓥)
η-is-embedding = {!!}

partial-map-classifer : (A ⇀ B) ≃ (A → ℒ (universeOf A ⊔ universeOf B) B)
partial-map-classifer = {!!}
-}
-- Kleene equality

_≅_ : {A : 𝓤 ̇} (p q : ℒ 𝓥 A) → 𝓤 ⊔ 𝓥 ⁺ ̇
_≅_ {A = A} p q = Σ[ p=q ꞉ p is-defined ≡ q is-defined ]
  PathP (λ i → ⟨ p=q i ⟩ → A) (value p) (value q) 

Kleeneto≡ : (p q : ℒ 𝓥 A)
  → p ≅ q
  → p ≡ q
Kleeneto≡ p q p≅q =
  p
    ≡⟨ refl ⟩
  (p is-defined , value p)
    ≡⟨ ΣPathP p≅q ⟩
  (q is-defined , value q)
    ≡⟨ refl ⟩
  q
    ∎

pure-is-defined : {A : 𝓤 ̇}
  → (a : A) → η 𝓥 a ↓
pure-is-defined a = tt*

defined-is-pure : {A : 𝓤 ̇} (p : ℒ 𝓥 A)
  → (p↓ : p ↓) 
  → Σ[ a ꞉ A ] p ≡ η 𝓥 a
defined-is-pure {A = A} p p↓ = 
  transport (λ i → ⟨ p↓=⊤ i ⟩ → A) (value p) tt* ,
    (p is-defined , value p
      ≡[ i ]⟨ p↓=⊤ i , transport-filler (λ i → ⟨ p↓=⊤ i ⟩ → A) (value p) i ⟩
    (Unit* , isPropUnit*) , (λ { tt* → transport (λ i → ⟨ p↓=⊤ i ⟩ → A) (value p) tt*})
      ∎) 
  where
    p↓=⊤ : p is-defined ≡ (Unit* , isPropUnit*)
    p↓=⊤ = ⇒∶ (λ _ → tt*)
           ⇐∶ (λ _ → p↓)
