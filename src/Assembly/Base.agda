{-# OPTIONS --without-K --cubical #-}

open import Prelude
  hiding (⊥)
open import Algebra.PCA
{- The notion of assembly is defined over a fixed partial combinatory algebra -}

module Assembly.Base (𝓥 : Universe) (A : PCA 𝓥 𝓤₀) where
open PcaStr (str A)
open IsPCA isPCA

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    _⊩_           : Π[ a ꞉ ⟨ A ⟩ ] Π[ _ ꞉ X ] 𝓤 ̇
    _isRealisable : Π[ x ꞉ X ] ∃[ a ꞉ ⟨ A ⟩ ] a ⊩ x

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Morphisms between assemblies

module Mor (X Y : Asm 𝓤) where
  open AsmStr (str X) renaming (_⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (_⊩_ to _⊩y_)
  
  record _Tracks_ (r : ⟨ A ⟩)(f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
    constructor tracks
    field
      tracks : (a : ⟨ A ⟩) (x : ⟨ X ⟩)
        → a ⊩x x
        → Σ[ p ꞉ r · a ↓ ] value (r · a) p ⊩y f x

  record HasTracker (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ⊔ 𝓥 ⁺ ̇ where 
    constructor istrackable
    field
      tracker : Σ[ r ꞉ ⟨ A ⟩ ] r Tracks f

  IsTrackable : (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ⊔ 𝓥 ⁺ ̇
  IsTrackable f = ∥ HasTracker f ∥

  record Trackable : 𝓤 ⊔ 𝓥 ⁺ ̇ where
    constructor trackable
    field
      fun         : ⟨ X ⟩ → ⟨ Y ⟩
      isTrackable : IsTrackable fun

------------------------------------------------------------------------------
-- Examples

_⊩⊥_ : ⟨ A ⟩ → Prelude.⊥ → 𝓤 ̇
_⊩⊥_ = λ a ()

⊥ : Asm₀
⊥ = _ , asmstr _⊩⊥_ λ ()

𝔄 : Asm 𝓤₀
𝔄 = ⟨ A ⟩ , asmstr _≡_ λ a → ∣ a , refl ∣

∇₀_ : (X : 𝓤 ̇) → Asm 𝓤
∇₀ X = X , asmstr _⊩∇_ ⊩∇-is-a-realisabiltiy
  where
    _⊩∇_ : ⟨ A ⟩ → X → (universeOf X) ̇
    a ⊩∇ x = Unit*

    ⊩∇-is-a-realisabiltiy : Π[ x ꞉ X ] ∃[ a ꞉ ⟨ A ⟩ ] a ⊩∇ x
    ⊩∇-is-a-realisabiltiy x =
      truncElim {P = λ _ → ∃[ a ꞉ ⟨ A ⟩ ] Unit*} (λ _ → propTruncIsProp)
      (λ a → ∣ a , tt* ∣)
      nonEmpty
