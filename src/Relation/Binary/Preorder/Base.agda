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

record IsPreorder {A : 𝓤 ̇} (_≼_ : Order A 𝓥) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor ispreorder
  field
    isReflexive  : isRefl _≼_
    isTransitive : isTrans _≼_
    ≼-isProp     : {x y : A} → isProp (x ≼ y)

record HasPreorder (𝓥 : Universe) (A : 𝓤 ̇) : (𝓤 ⊔ 𝓥) ⁺  ̇ where
  constructor _,_
  field
    _≼_          : Order A 𝓥
    ≼-isPreorder : IsPreorder _≼_
  open IsPreorder ≼-isPreorder public

Preordered : (𝓥 𝓤 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Preordered 𝓥 𝓤 = TypeWithStr 𝓤 (HasPreorder 𝓥)

Preordered₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
Preordered₀ 𝓥 = TypeWithStr 𝓤₀ (HasPreorder 𝓥)

ℒᵖ : Preordered 𝓥 𝓤 → Preordered 𝓥 (𝓤 ⊔ 𝓥 ⁺)
ℒᵖ (A , _≼_ , ≼-isPreorder) = ℒ _ A , ℒᵖ-Order _≼_ , ℒ-Order-isPreorder ≼-isPreorder
  where
    open IsPreorder

    ℒᵖ-Order : (_≼_ : Order A 𝓥) → Order (ℒ 𝓥 A) 𝓥
    ℒᵖ-Order _≼_ x y = (y↓ : y ↓) → Σ[ x↓ ꞉ x ↓ ] (value x x↓ ≼ value y y↓)

    ℒ-Order-isPreorder : {_≼_ : Order A 𝓥} → IsPreorder _≼_ → IsPreorder (ℒᵖ-Order _≼_)
    isReflexive  (ℒ-Order-isPreorder ≼-isOrdered) x x↓ = x↓ , isReflexive ≼-isOrdered (value x x↓)
    isTransitive (ℒ-Order-isPreorder ≼-isOrdered) x y z x≼y y≼z z↓ =
      let y↓  = y≼z z↓ .fst
          y≤z = y≼z z↓ .snd
          x↓  = x≼y y↓ .fst
          x≤y = x≼y y↓ .snd
      in x↓ , isTransitive ≼-isOrdered (value x x↓) (value y y↓) (value z z↓) x≤y y≤z
    ≼-isProp     (ℒ-Order-isPreorder ≼-isOrdered) {x} {y} = isPropΠ λ y↓ →
      isPropΣ (x ↓-isProp) λ x↓ → ≼-isProp ≼-isOrdered
