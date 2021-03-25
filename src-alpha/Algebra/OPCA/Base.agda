{-# OPTIONS --without-K --cubical #-}

module Algebra.OPCA.Base where

open import Prelude
  hiding ([_])
open import Relation.Binary.Preorder
open import Function.Partial               public

open import Algebra.OPAS.Base              public

private
  variable
    n m : ℕ
    
record IsOPCA 𝓥 {A : 𝓤 ̇} (_≼_ : Order A 𝓥) (_·_ : A → A → ℒ 𝓥 A) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    isOPAS : IsOPAS 𝓥 _≼_ _·_
  open IsOPAS isOPAS  public
  field
    ƛ_     : Term A (suc n) → Term A n
    completeness : {t : Term A (suc n)} {a : A} {as : Finite A n}
      → ⟦ (ƛ t) ⊙ ᶜ a ⟧ as ℒ≼ ⟦ t ⟧ (a ∷ as)
  infixr  5 ƛ_

record OpcaStr (𝓥 : Universe) (A : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  constructor opcastr
  field
    _≼_    : Order A 𝓥
    _·_    : A → A → ℒ 𝓥 A
    isOPCA : IsOPCA 𝓥 _≼_ _·_ 
  infixl 7 _·_

  open IsOPCA isOPCA public

  opasStr : OpasStr 𝓥 A
  opasStr = passtr _≼_ _·_ isOPAS
open OpcaStr
  
OPCA : (𝓥 𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
OPCA 𝓥 𝓤 = TypeWithStr 𝓤 (OpcaStr 𝓥)

OPCA₀ : (𝓥 : Universe) → 𝓤₁ ⊔ 𝓥 ⁺ ̇
OPCA₀ 𝓥 = OPCA 𝓥 𝓤₀

OPCA→OPAS : OPCA 𝓥 𝓤 → OPAS 𝓥 𝓤
OPCA→OPAS (A , opcaStr) = A , opasStr opcaStr
