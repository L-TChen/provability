{-# OPTIONS --without-K --cubical #-}

module Relation.Binary.Preorder.Base where
open import Cubical.Relation.Binary
open BinaryRelation

open import Prelude
open import Function.Partial

Order : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
Order A 𝓥 = Rel A A 𝓥

private
  variable
    A   : 𝓤 ̇
    _≼_ : Order A 𝓥

record IsPreordered {A : 𝓤 ̇} (_≼_ : Order A 𝓥) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor ispreordered
  field
    isReflexive  : isRefl _≼_
    isTransitive : isTrans _≼_
    ≼-isProp     : {x y : A} → isProp (x ≼ y)

ℒᵖ : (_≼_ : Order A 𝓥) → Order (ℒ 𝓥 A) 𝓥
ℒᵖ _≼_ x y = (y↓ : y ↓) → Σ[ x↓ ꞉ x ↓ ] (value x x↓ ≼ value y y↓)

module _ where
  open IsPreordered 

  ℒ-Order-isPreorder : IsPreordered _≼_ → IsPreordered (ℒᵖ _≼_)
  isReflexive  (ℒ-Order-isPreorder ≼-isOrdered) x x↓ = x↓ , isReflexive ≼-isOrdered (value x x↓)
  isTransitive (ℒ-Order-isPreorder ≼-isOrdered) x y z x≼y y≼z z↓ =
    let y↓  = y≼z z↓ .fst
        y≤z = y≼z z↓ .snd
        x↓  = x≼y y↓ .fst
        x≤y = x≼y y↓ .snd
    in x↓ , isTransitive ≼-isOrdered (value x x↓) (value y y↓) (value z z↓) x≤y y≤z
  ≼-isProp     (ℒ-Order-isPreorder ≼-isPreordered) {x} {y} =
    isPropΠ (λ y↓ → isPropΣ (x ↓isProp) λ x↓ → ≼-isProp ≼-isPreordered)
