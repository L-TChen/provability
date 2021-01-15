{-# OPTIONS --without-K --cubical #-}


open import Prelude
open import Cubical.HITs.PropositionalTruncation
import Cubical.Data.Empty                   as E

open import Algebra.PCA

{- The notion of assembly is defined over a fixed partial combinatory algebra -}

module Assembly.Base (A : PCA 𝓥) where

open PcaStr (str A)

record IsAssembly {X : 𝓤 ̇} (_⊩_ : ⟨ A ⟩ → X → 𝓤 ⊔ 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where 
  field
    isRealisable : (x : X) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩ x)

record AsmStr (X : 𝓤 ̇) : (𝓤 ⊔ 𝓥)⁺ ̇ where
  field
    _⊩_        : ⟨ A ⟩ → X → 𝓤 ⊔ 𝓥 ̇
    isAssembly : IsAssembly _⊩_

  open IsAssembly isAssembly

Asm : (𝓤 : Level) → (𝓤 ⊔ 𝓥)⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ⊔ 𝓥 ⁺  ̇
Asm₀ = Asm 𝓤₀

⊥ : Asm₀
⊥ = E.⊥ , record
  { _⊩_        = λ _ ()
  ; isAssembly = record
    { isRealisable = λ () }
  }

record IsTrackable {X : Asm 𝓤} {Y : Asm 𝓤} (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ⊔ 𝓥 ̇ where 
  open AsmStr (str X) renaming (_⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (_⊩_ to _⊩y_)
  field
    isTrackable : ∃[ r ∈ ⟨ A ⟩ ] ∀ (a : ⟨ A ⟩) (x : ⟨ X ⟩)
      → a ⊩x x → Σ[ p ∈ r · a ↓ ] value (r · a) p ⊩y f x

record Trackable {X : Asm 𝓤} {Y : Asm 𝓤} : 𝓤 ⊔ 𝓥 ̇ where
  field
    fun         : ⟨ X ⟩ → ⟨ Y ⟩
    isTrackable : IsTrackable {𝓤} {X} {Y} fun

