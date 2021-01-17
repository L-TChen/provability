{-# OPTIONS --without-K --cubical #-} 

open import Prelude

module Function.Partial.Base where

open import Cubical.Relation.Binary
open import Cubical.Functions.Embedding

module _ {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (x : X) → isProp (Σ[ y ∈ Y ] R x y)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
X ⇀ Y = Σ[ R ∈ _ ] Σ[ e ∈ (R → X) ] isEmbedding e × (R → Y) 

record ℒ_ (X : 𝓤 ̇) : 𝓤 ⊔ 𝓤₁ ̇ where
  constructor partial
  field
    P       : 𝓤₀ ̇
    PisProp : isProp P
    value   : P → X
open ℒ_ renaming (P to _↓; PisProp to _↓isProp) public

_is-defined : ℒ X → 𝓤₀ ̇
_is-defined = ℒ_.P

instance
  Functorℒ : Functor ℒ_
  _<$>_ ⦃ Functorℒ ⦄ f (partial P PisProp x) = partial P PisProp (f ∘ x)
  
  Monadℒ : Monad ℒ_
  return ⦃ Monadℒ ⦄ x   = partial Unit* isPropUnit* λ _ → x
  _>>=_  ⦃ Monadℒ ⦄ x f = partial Q QisProp y
    where
      Q = Σ[ p ∈ x is-defined ] (f (value x p) ↓)

      QisProp : isProp Q
      QisProp = isPropΣ (x ↓isProp) λ p → f (value x p) ↓isProp

      y : Q → _
      y (p , fx↓) = value (f (value x p)) fx↓

  Applicativeℒ : Applicative ℒ_
  Applicativeℒ = Monad⇒Applicative
