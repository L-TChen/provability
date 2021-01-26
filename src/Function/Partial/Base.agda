{-# OPTIONS --without-K --cubical #-} 

module Function.Partial.Base where

open import Cubical.Relation.Binary
open import Cubical.Functions.Embedding
open import Cubical.Data.Nat

open import Prelude

infix 2 _↓ _↓isProp

private
  variable
    A B : 𝓤 ̇

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} (R : A → B → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (a : A) → isProp (Σ[ b ꞉ B ] R a b)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
A ⇀ B = Σ[ R ꞉ universeOf A ⊔ universeOf B ̇ ] Σ[ e ꞉ (R → A) ] isEmbedding e × (R → B)

record ℒ (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor partial
  field
    _is-defined            : 𝓥 ̇
    definedness-of_is-Prop : isProp (_is-defined)
    value       : _is-defined → A
open ℒ public

_↓ : {A : 𝓤 ̇} → ℒ 𝓥 A → 𝓥 ̇
x ↓ = x ℒ.is-defined

_↓isProp : {A : 𝓤 ̇}
  → (x : ℒ 𝓥 A) → isProp (x ↓)
x ↓isProp = ℒ.definedness-of x is-Prop 

undefined : ℒ 𝓥 A
_is-defined            undefined = ⊥*
definedness-of_is-Prop undefined ()
 
instance
  Functorℒ : Functor (𝓥 ⁺) (ℒ 𝓥)
  _<$>_ ⦃ Functorℒ ⦄ f (partial P PisProp x) = partial P PisProp (f ∘ x) 
  
  Monadℒ : Monad (𝓥 ⁺) (ℒ 𝓥)
  return ⦃ Monadℒ ⦄ x   = partial Unit* isPropUnit* (λ _ → x)
  _>>=_  ⦃ Monadℒ ⦄ {X = A} {Y = B} x f = partial Q QisProp y
    where
      Q = Σ[ p ꞉ x ↓ ] f (value x p) ↓

      QisProp : isProp Q
      QisProp = isPropΣ (x ↓isProp) λ x↓ → f (value x x↓) ↓isProp

      y : Q → B
      y (x↓ , fx↓) = value (f (value x x↓)) fx↓

  Applicativeℒ : Applicative (𝓥 ⁺) (ℒ 𝓥)
  Applicativeℒ = Monad⇒Applicative
 
pure-is-defined : {A : 𝓤 ̇} (a : A) → _↓ {𝓤} {𝓥} (pure a)
pure-is-defined a = tt*

--⟪_⟫ : (ℕ → Bool) → 𝓤₀ ̇
--⟪ α ⟫ = Σ[ n ꞉ ℕ ] α n ≡ true
--
--_isRosolini : 𝓤 ̇ → 𝓤 ⁺ ̇
--A isRosolini = ∃[ α ꞉ (ℕ → Bool) ] isProp ⟪ α ⟫ × (A ≡ Lift ⟪ α ⟫)

record Dominance : 𝓤 ⁺ ̇ where
  constructor dominance
  field
    d              : 𝓤 ̇ → 𝓤 ̇
    d-is-prop      : Π[ A ꞉ 𝓤 ̇ ] isProp (d A)
    dx-is-prop     : Π[ A ꞉ 𝓤 ̇ ] (d A → isProp A)
    d1-is-dominant : d Unit*
    Σ-dominat-type : Π[ P ꞉ 𝓤 ̇ ] Π[ Q ꞉ (P → 𝓤 ̇) ] (d P → Π[ p ꞉ P ] d (Q p) → d (Σ[ p ꞉ P ] Q p))
