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

record ℒ_ (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor partial
  field
    P       : 𝓤 ̇
    PisProp : isProp P
    value   : P → X
open ℒ_ renaming (P to _↓; PisProp to _↓isProp) public

_is-defined : ℒ X → (universeOf X) ̇
_is-defined = ℒ_.P

unitℒ : X → ℒ X
unitℒ x = partial Unit* isPropUnit* λ _ → x

bindℒ : {X Y : 𝓤 ̇}
  → ℒ X → (X → ℒ Y) → ℒ Y
bindℒ {Y = Y} x f = partial Q QisProp y
  where
    Q = Σ[ p ∈ x is-defined ] (f (value x p) ↓)

    QisProp : isProp Q
    QisProp = isPropΣ (x ↓isProp) λ p → f (value x p) ↓isProp

    y : Q → Y
    y (p , fx↓) = value (f (value x p)) fx↓
