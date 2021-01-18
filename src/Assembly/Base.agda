{-# OPTIONS --without-K --cubical #-}

open import Prelude
open import Algebra.PCA
{- The notion of assembly is defined over a fixed partial combinatory algebra -}
module Assembly.Base (𝓥 : Universe) (A : PCA 𝓥 𝓤₀) where
open PcaStr (str A)

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    _⊩_           : ⟨ A ⟩ → X → 𝓤 ̇
    _isRealisable : (x : X) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩ x)

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀
