{-# OPTIONS --without-K --cubical #-} 

module Function.Partial.Base where

open import Cubical.Relation.Binary
open import Cubical.Functions.Embedding
open import Cubical.Data.Nat

open import Prelude

infix 2 _↓ _↓isProp _is-defined

private
  variable
    X : 𝓤 ̇

module _ {X : 𝓤 ̇} {Y : 𝓥 ̇} (R : X → Y → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (x : X) → isProp (Σ[ y ꞉ Y ] R x y)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
X ⇀ Y = Σ[ R ꞉ universeOf X ⊔ universeOf Y ̇ ] Σ[ e ꞉ (R → X) ] isEmbedding e × (R → Y)

record ℒ (𝓥 : Universe) (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor partial
  field
    P       : 𝓥 ̇
    PisProp : isProp P
    value   : P → X

open ℒ using (value) public

_↓ : {X : 𝓤 ̇} → ℒ 𝓥 X → 𝓥 ̇
x ↓ = ℒ.P x

_↓isProp : {X : 𝓤 ̇}
  → (x : ℒ 𝓥 X) → isProp (x ↓)
x ↓isProp = ℒ.PisProp x

_is-defined : {X : 𝓤 ̇} → ℒ 𝓥 X → 𝓥 ̇
_is-defined = ℒ.P

undefined : ℒ 𝓥 X
ℒ.P       undefined = ⊥*
ℒ.PisProp undefined ()
ℒ.value   undefined ()
 
--⟪_⟫ : (ℕ → Bool) → 𝓤₀ ̇
--⟪ α ⟫ = Σ[ n ꞉ ℕ ] α n ≡ true
--
--_isRosolini : 𝓤 ̇ → 𝓤 ⁺ ̇
--A isRosolini = ∃[ α ꞉ (ℕ → Bool) ] isProp ⟪ α ⟫ × (A ≡ Lift ⟪ α ⟫)

record Dominance : 𝓤 ⁺ ̇ where
  constructor dominance
  field
    d              : 𝓤 ̇ → 𝓤 ̇
    d-is-prop      : Π[ X ꞉ 𝓤 ̇ ] isProp (d X)
    dx-is-prop     : Π[ X ꞉ 𝓤 ̇ ] (d X → isProp X)
    d1-is-dominant : d Unit*
    Σ-dominat-type : Π[ P ꞉ 𝓤 ̇ ] Π[ Q ꞉ (P → 𝓤 ̇) ] (d P → Π[ p ꞉ P ] d (Q p) → d (Σ[ p ꞉ P ] Q p))

instance
  Functorℒ : Functor (𝓥 ⁺) (ℒ 𝓥)
  _<$>_ ⦃ Functorℒ ⦄ f (partial P PisProp x) = partial P PisProp (f ∘ x)
  
  Monadℒ : Monad (𝓥 ⁺) (ℒ 𝓥)
  return ⦃ Monadℒ ⦄ x   = partial Unit* isPropUnit* (λ _ → x)
  _>>=_  ⦃ Monadℒ ⦄ x f = partial Q QisProp y
    where
      Q = Σ[ p ꞉ x ↓ ] f (value x p) ↓

      QisProp : isProp Q
      QisProp = isPropΣ (x ↓isProp) λ x↓ → f (value x x↓) ↓isProp

      y : Q → _
      y (p , fx↓) = value (f (value x p)) fx↓

  Applicativeℒ : Applicative (𝓥 ⁺) (ℒ 𝓥)
  Applicativeℒ = Monad⇒Applicative
 
