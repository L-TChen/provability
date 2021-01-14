{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude

open import Algebra.PCA

open import Cubical.Data.Empty                   as E
  hiding (⊥)

module _ (A : PAS ℓ₀) where
  record IsAssembly {X : Type ℓ} (_⊩_ : typ A → X → Type (ℓ-max ℓ₀ ℓ)) : Type (ℓ-max ℓ₀ ℓ) where 
    field
      isRealisable : (x : X) → ∃[ a ∈ typ A ] (a ⊩ x)
      ⊩isProp       : (a : typ A) (x : X) → isProp (a ⊩ x)

-- record Asm : 𝓤₁ where
--   infix 6 _⊩_
--   field
--     Carrier    : 𝓤
--     {type}     : Type
--     _⊩_        : Prog type → Carrier → 𝓤

--     realiserOf : isRealisable Carrier _⊩_

--   RealisabilityIsProp : isProp (isRealisable Carrier _⊩_)
--   RealisabilityIsProp = isPropΠ (λ _ → propTruncIsProp)
-- open Asm using (type; Carrier) 

-- track : (X Y : Asm) → Prog (X .type →̇ Y .type)
--   → (X .Carrier → Y .Carrier) → 𝓤
-- track X Y L h = ∀ M x → M ⊩x x → Σ[ N ∈ _ ] (∅ ⊢ L · M -↠ N) C.× N ⊩y h x
--   where
--     open Asm X renaming (_⊩_ to _⊩x_)
--     open Asm Y renaming (_⊩_ to _⊩y_)

-- IsTrackable : (A B : Asm) → (A .Carrier → B .Carrier) → 𝓤
-- IsTrackable X Y h = Σ[ L ∈ _ ] track X Y L h

-- Trackable : (A B : Asm) → 𝓤
-- Trackable X Y = Σ[ f ∈ _ ] IsTrackable X Y f
