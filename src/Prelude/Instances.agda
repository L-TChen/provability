{-# OPTIONS --without-K --cubical --no-import-sorts #-}

module Prelude.Instances where

open import Cubical.Foundations.Prelude 
open import Cubical.Relation.Nullary

open import Prelude.Universes

record Coercion (A : 𝓤 ̇) (B : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
  field
    ⟨_⟩ : A → B
open Coercion ⦃ ... ⦄ public

{-# DISPLAY Coercion.⟨_⟩ A = A  #-}

--record IsProp (A : 𝓤 ̇) : 𝓤 ̇ where
--  field
--    isProp : Cubical.isProp A
--open IsProp ⦃ ... ⦄ public
--
--{-# DISPLAY IsProp.isProp A = isProp A  #-}
--
--record IsSet (A : 𝓤 ̇) : 𝓤 ̇ where
--  field
--    isSet : Cubical.isSet A
--open IsSet ⦃ ... ⦄ public
--
--{-# DISPLAY IsSet.isSet A = isSet A  #-}

record IsDiscrete (A : 𝓤 ̇) : 𝓤 ̇ where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

  ≟→isSet : isSet A
  ≟→isSet = Discrete→isSet _≟_
open IsDiscrete ⦃ ... ⦄ public

{-# DISPLAY IsDiscrete._≟_ x y = x ≟ y #-}
