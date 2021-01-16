{-# OPTIONS --without-K --cubical #-}

open import Prelude
open import Algebra.PCA

module Assembly.Trackable (A : PCA 𝓤₀) where

open import Assembly.Base A
open PcaStr (str A)

record IsTrackable (X : Asm 𝓤) (Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where 
  constructor istrackable

  open AsmStr (str X) renaming (_⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (_⊩_ to _⊩y_)
  field
    isTrackable : ∃[ r ∈ ⟨ A ⟩ ]
        ∀ (a : ⟨ A ⟩) (x : ⟨ X ⟩)
      → a ⊩x x
      → Σ[ p ∈ r · a ↓ ] value (r · a) p ⊩y f x

record Trackable (X : Asm 𝓤) (Y : Asm 𝓤) : 𝓤 ̇ where
  constructor trackable
  field
    fun         : ⟨ X ⟩ → ⟨ Y ⟩
    isTrackable : IsTrackable X Y fun
