{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

module Function.Partial.Properties where

import Cubical.Functions.Logic as L

open import Prelude
open import Function.Partial.Base

partial-map-classifer : {X Y : 𝓤 ̇}
  → (X ⇀ Y) ≃ (X → ℒ (universeOf X ⊔ universeOf Y) Y)
partial-map-classifer = {!!}

pure-is-defined : {A : 𝓤 ̇}
  → (a : A) → ⟨ _↓ {𝓥} {𝓤} (pure a) ⟩
pure-is-defined a = tt*

defined-is-pure : {A : 𝓤 ̇}
  → (p : ℒ 𝓥 A) → (p↓ : ⟨ p ↓ ⟩) 
  → Σ[ a ꞉ A ] p ≡ pure a
defined-is-pure {𝓥 = 𝓥} {A = A} p p↓ = transport (λ i → ⟨ p↓≡⊤ i ⟩ → A) (value p) tt* ,
    (p is-defined , value p
      ≡[ i ]⟨ p↓≡⊤ i , transport-filler (λ i → ⟨ p↓≡⊤ i ⟩ → A) (value p) i ⟩
    L.⊤* , (λ _ → transport (λ i → ⟨ p↓≡⊤ i ⟩ → A) (value p) tt*)
      ∎) 
  where
    open L
    p↓≡⊤ : p is-defined ≡ ⊤*
    p↓≡⊤ = ⇒∶ (λ _ → tt*)
           ⇐∶ (λ _ → p↓)
