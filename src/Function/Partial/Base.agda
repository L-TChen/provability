{-# OPTIONS --without-K --cubical  --allow-unsolved-metas #-} 

module Function.Partial.Base where

open import Cubical.Functions.Embedding
import Cubical.Functions.Logic as L

open import Prelude

infix 2 _↓ 

private
  variable
    A B : 𝓤 ̇

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} (R : A → B → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (a : A) → isProp (Σ[ b ꞉ B ] R a b)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
A ⇀ B = Σ[ R ꞉ universeOf A ⊔ universeOf B ̇ ] Σ[ e ꞉ (R → A) ] isEmbedding e × (R → B)

record ℒ (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor _,_
  field
    _is-defined : hProp 𝓥
    value       : ⟨ _is-defined ⟩ → A
open ℒ public

_↓ : ℒ 𝓥 A → hProp 𝓥
x ↓ = (x ℒ.is-defined)

undefined : ℒ 𝓥 A
_is-defined undefined = ⊥* , λ ()
 
instance
  Functorℒ : Functor (𝓥 ⁺) (ℒ 𝓥)
  _<$>_ ⦃ Functorℒ ⦄ f (P , x) = P , (f ∘ x) 
  
  Monadℒ : Monad (𝓥 ⁺) (ℒ 𝓥)
  return ⦃ Monadℒ ⦄ x   = L.⊤* , (λ _ → x)
  _>>=_  ⦃ Monadℒ ⦄ {X = A} {Y = B} x f = (Q , QisProp) , y
    where
      Q = Σ[ p ꞉ ⟨ x ↓ ⟩ ] ⟨ f (value x p) ↓ ⟩

      QisProp : isProp Q
      QisProp = isPropΣ (L.isProp⟨⟩ (x ↓)) λ x↓ → L.isProp⟨⟩ (f (value x x↓) ↓)

      y : Q → B
      y (x↓ , fx↓) = value (f (value x x↓)) fx↓

  Applicativeℒ : Applicative (𝓥 ⁺) (ℒ 𝓥)
  Applicativeℒ = Monad⇒Applicative
 
pure-is-defined : {A : 𝓤 ̇}
  → (a : A) → ⟨ _↓ {𝓥} {𝓤} (pure a) ⟩
pure-is-defined a = tt*

defined-is-pure : {A : 𝓤 ̇}
  → (v : ℒ 𝓥 A) → (v↓ : ⟨ v ↓ ⟩)
  → Σ[ a ꞉ A ] v ≡ pure a
defined-is-pure {𝓥 = 𝓥} {A = A} v v↓ = value v v↓ , (
  v is-defined , value v
    ≡[ i ]⟨ v↓≡⊤ i , single-value i ⟩
  ⊤* , (λ _ → value v v↓)
    ∎)
  where
    open L
    v↓≡⊤ : v is-defined ≡ ⊤*
    v↓≡⊤ = ⇒∶ (λ _ → tt*)
           ⇐∶ (λ _ → v↓)

    single-value : PathP (λ i → ⟨ v↓≡⊤ i ⟩ → A) (value v) (λ _ → value v v↓)
    single-value = {!!}

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
