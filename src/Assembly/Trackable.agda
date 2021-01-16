{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

open import Prelude
open import Algebra.PCA

module Assembly.Trackable (A : PCA 𝓤₀) where

open import Assembly.Base A
open PcaStr (str A)
open IsPCA isPCA

module _ (X Y : Asm 𝓤) where
  open AsmStr (str X) renaming (_⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (_⊩_ to _⊩y_)
  
  _tracks_ : ⟨ A ⟩ → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  _tracks_ r f = ∀ (a : ⟨ A ⟩) (x : ⟨ X ⟩)
    → Σ[ p ∈ (r · a) ↓ ] (value (r · a) p ⊩y f x) 

  record IsTrackable (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where 
    constructor istrackable
    field
      tracker : ∃[ r ∈ ⟨ A ⟩ ] r tracks f

  record Trackable : 𝓤 ̇ where
    constructor trackable
    field
      fun         : ⟨ X ⟩ → ⟨ Y ⟩
      isTrackable : IsTrackable fun

id : (X : Asm 𝓤) → Trackable X X
id X = trackable (λ x → x) (istrackable {!!})
