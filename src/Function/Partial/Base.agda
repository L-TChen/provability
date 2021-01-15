{-# OPTIONS --without-K --cubical #-} 

module Function.Partial.Base where

open import Prelude

open import Cubical.Relation.Binary
open import Cubical.Data.Unit

open import Cubical.Functions.Embedding

module _ {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (x : X) → isProp (Σ[ y ∈ Y ] R x y)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
X ⇀ Y = Σ[ R ∈ _ ] Σ[ e ∈ (R → X) ] isEmbedding e × (R → Y) 

ℒ_ : 𝓤 ̇ → 𝓤 ⁺ ̇ 
ℒ Y = Σ[ P ∈ _ ] (isProp P × (P → Y))

extent : ℒ Y → (universe-of Y) ̇
extent (P , _) = P

value : (u : ℒ Y) → (extent u) → Y
value (P , _ , f) = f
