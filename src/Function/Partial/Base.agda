{-# OPTIONS --without-K --cubical #-} 

module Function.Partial.Base where

open import Prelude

open import Cubical.Relation.Binary
open import Cubical.Data.Unit

open import Cubical.Functions.Embedding

module _ {X : Type ℓ₁} {Y : Type ℓ₂} (R : X → Y → Type (ℓ-max ℓ₁ ℓ₂)) where
  isFunctional : Type (ℓ-max ℓ₁ ℓ₂)
  isFunctional = (x : X) → isProp (Σ[ y ∈ Y ] R x y)

_⇀_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
X ⇀ Y = Σ[ R ∈ Type _ ] Σ[ e ∈ (R → X) ] isEmbedding e × (R → Y) 

ℒ_ : Type ℓ → Type (ℓ-suc ℓ)
ℒ Y = Σ[ P ∈ Type _ ] (isProp P × (P → Y))

extent : ℒ Y → Type _
extent (P , _) = P

value : (u : ℒ Y) → (extent u) → Y
value (P , _ , f) = f
