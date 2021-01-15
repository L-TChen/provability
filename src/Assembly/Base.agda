{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty                   as E
  hiding (⊥)

open import Algebra.PCA

{- The notion of assembly is defined over a fixed partial combinatory algebra -}

module _ (A : PCA 𝓥) where
  record IsAssembly {X : 𝓤 ̇} (_⊩_ : ⟨ A ⟩ → X → 𝓤 ⊔ 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where 
    field
      isRealisable : ∀ (x : X) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩ x)

    ⊩isProp : ∀ (a : ⟨ A ⟩) (x : X) → isProp (a ⊩ x)
    ⊩isProp = {!isPropΠ (λ _ → propTruncIsProp)!}

  record AsmStr (X : 𝓤 ̇) : (𝓤 ⊔ 𝓥)⁺ ̇ where
     field
       _⊩_        : ⟨ A ⟩ → X → 𝓤 ⊔ 𝓥 ̇
       isAssembly : IsAssembly _⊩_

     open IsAssembly isAssembly

  Asm : (𝓤 : Level) → (𝓤 ⊔ 𝓥)⁺ ̇ -- Type (ℓ-suc (ℓ-max ℓ₀ ℓ))
  Asm 𝓤 = TypeWithStr 𝓤 AsmStr

  Asm₀ : 𝓤₁ ⊔ 𝓥 ⁺  ̇
  Asm₀ = Asm 𝓤₀
-- -- record Asm : 𝓤₁ where
-- --   infix 6 _⊩_
-- --   field
-- --     Carrier    : 𝓤
-- --     {type}     : Type
-- --     _⊩_        : Prog type → Carrier → 𝓤

-- --     realiserOf : isRealisable Carrier _⊩_

-- --   RealisabilityIsProp : isProp (isRealisable Carrier _⊩_)
-- --   RealisabilityIsProp = isPropΠ (λ _ → propTruncIsProp)
-- -- open Asm using (type; Carrier) 

-- -- track : (X Y : Asm) → Prog (X .type →̇ Y .type)
-- --   → (X .Carrier → Y .Carrier) → 𝓤
-- -- track X Y L h = ∀ M x → M ⊩x x → Σ[ N ∈ _ ] (∅ ⊢ L · M -↠ N) C.× N ⊩y h x
-- --   where
-- --     open Asm X renaming (_⊩_ to _⊩x_)
-- --     open Asm Y renaming (_⊩_ to _⊩y_)

-- -- IsTrackable : (A B : Asm) → (A .Carrier → B .Carrier) → 𝓤
-- -- IsTrackable X Y h = Σ[ L ∈ _ ] track X Y L h

-- -- Trackable : (A B : Asm) → 𝓤
-- -- Trackable X Y = Σ[ f ∈ _ ] IsTrackable X Y f
