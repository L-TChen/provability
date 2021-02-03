{-# OPTIONS --without-K --cubical #-} 

module Function.Partial.Base where

open import Cubical.Functions.Embedding
import Cubical.Functions.Logic as L

open import Prelude


private
  variable
    A B : 𝓤 ̇

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} (R : A → B → 𝓤 ⊔ 𝓥 ̇) where
  isFunctional : 𝓤 ⊔ 𝓥 ̇
  isFunctional = (a : A) → isProp (Σ[ b ꞉ B ] R a b)

_⇀_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
A ⇀ B = Σ[ R ꞉ universeOf A ⊔ universeOf B ̇ ] Σ[ e ꞉ (R → A) ] isEmbedding e × (R → B)

--record ℒ (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
--  constructor _,_
--  field
--    _is-defined : hProp 𝓥
--    value       : ⟨ _is-defined ⟩ → A
--open ℒ public

infix 5 _↓

ℒ : (𝓥 : Universe) (A : 𝓤 ̇) → 𝓤 ⊔ 𝓥 ⁺ ̇ 
ℒ 𝓥 A = Σ[ P ꞉ hProp 𝓥 ] (⟨ P ⟩ → A)

_is-defined : ℒ 𝓥 A → hProp 𝓥
x is-defined = x .fst

_↓ : ℒ 𝓥 A → 𝓥 ̇
x ↓ = x .fst .fst

_↓-isProp : (p : ℒ 𝓥 A) → isProp ((p ↓))
p ↓-isProp = p .fst .snd

value : (p : ℒ 𝓥 A) → p ↓ → A
value = snd

undefined : ℒ 𝓥 A
fst undefined = ⊥* , λ ()
 
η : (𝓥 : Universe) → A → ℒ 𝓥 A
η 𝓥 a = (Unit* , isPropUnit*) , λ _ → a

instance
  Functorℒ : Functor (𝓥 ⁺) (ℒ 𝓥)
  _<$>_ ⦃ Functorℒ ⦄ f (P , x) = P , (f ∘ x) 

  Monadℒ : Monad (𝓥 ⁺) (ℒ 𝓥)
  return ⦃ Monadℒ ⦄ = η _
  _>>=_  ⦃ Monadℒ ⦄ {X = A} {Y = B} x f = (Q , QisProp) , y
    where
      Q = Σ[ p ꞉ x ↓ ] f (value x p) ↓ 

      QisProp : isProp Q
      QisProp = isPropΣ
        (L.isProp⟨⟩ (x ↓ , x ↓-isProp)) λ x↓ → L.isProp⟨⟩ (f (value x x↓) ↓ , (f (value x x↓) ↓-isProp)) 

      y : Q → B
      y (x↓ , fx↓) = value (f (value x x↓)) fx↓

  Applicativeℒ : Applicative (𝓥 ⁺) (ℒ 𝓥)
  Applicativeℒ = Monad⇒Applicative

{-# DISPLAY IxMonad.return = η  #-}

-- --⟪_⟫ : (ℕ → Bool) → 𝓤₀ ̇
-- --⟪ α ⟫ = Σ[ n ꞉ ℕ ] α n ≡ true
-- --
-- --_isRosolini : 𝓤 ̇ → 𝓤 ⁺ ̇
-- --A isRosolini = ∃[ α ꞉ (ℕ → Bool) ] isProp ⟪ α ⟫ × (A ≡ Lift ⟪ α ⟫)

-- record Dominance : 𝓤 ⁺ ̇ where
--   constructor dominance
--   field
--     d              : 𝓤 ̇ → 𝓤 ̇
--     d-is-prop      : Π[ A ꞉ 𝓤 ̇ ] isProp (d A)
--     dx-is-prop     : Π[ A ꞉ 𝓤 ̇ ] (d A → isProp A)
--     d1-is-dominant : d Unit*
--     Σ-dominat-type : Π[ P ꞉ 𝓤 ̇ ] Π[ Q ꞉ (P → 𝓤 ̇) ] (d P → Π[ p ꞉ P ] d (Q p) → d (Σ[ p ꞉ P ] Q p))
