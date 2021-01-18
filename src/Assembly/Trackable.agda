{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}

open import Prelude
  hiding (id)
open import Algebra.PCA

module Assembly.Trackable (𝓥 : Universe) (A : PCA 𝓥 𝓤₀) where

open import Assembly.Base 𝓥 A
open PcaStr (str A)
open IsPCA isPCA

module Mor (X Y : Asm 𝓤) where
  open AsmStr (str X) renaming (_⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (_⊩_ to _⊩y_)
  
  record _Tracks_ (r : ⟨ A ⟩)(f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
    constructor tracks
    field
      tracks : (a : ⟨ A ⟩) (x : ⟨ X ⟩)
        → a ⊩x x
        → Σ[ p ∈ (r · a) ↓ ] value (r · a) p ⊩y f x

  record HasTracker (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ⊔ 𝓥 ⁺ ̇ where 
    constructor istrackable
    field
      tracker : Σ[ r ∈ ⟨ A ⟩ ] r Tracks f

  IsTrackable : (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ⊔ 𝓥 ⁺ ̇
  IsTrackable f = ∥ HasTracker f ∥

  record Trackable : 𝓤 ⊔ 𝓥 ⁺ ̇ where
    constructor trackable
    field
      fun         : ⟨ X ⟩ → ⟨ Y ⟩
      isTrackable : IsTrackable fun
