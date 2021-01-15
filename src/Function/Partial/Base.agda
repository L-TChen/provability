{-# OPTIONS --without-K --cubical #-} 

module Function.Partial.Base where

open import Prelude

open import Cubical.Relation.Binary
open import Cubical.Data.Unit

open import Cubical.Functions.Embedding

infix 6 _↓

module _ {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (x : X) → isProp (Σ[ y ∈ Y ] R x y)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
X ⇀ Y = Σ[ R ∈ _ ] Σ[ e ∈ (R → X) ] isEmbedding e × (R → Y) 

ℒ_ : 𝓤 ̇ → 𝓤 ⁺ ̇ 
ℒ Y = Σ[ P ∈ (universe-of Y) ̇ ] (isProp P × (P → Y))

_is-defined : ℒ X → (universe-of X) ̇
(P , φ , x) is-defined = P

_↓ = _is-defined

value : (u : ℒ Y) → (u is-defined) → Y
value (P , _ , f) = f

η : X → ℒ X
η x = Lift Unit , (λ { (lift tt) (lift tt) i → lift tt }) , (λ _ → x)
