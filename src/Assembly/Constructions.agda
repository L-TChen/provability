{-# OPTIONS --without-K --cubical #-}

open import Prelude
open import Algebra.PCA

module Assembly.Constructions (A : PCA 𝓥 𝓤₀) where

open import Cubical.Data.Empty
  renaming (⊥ to Empty)
open import Cubical.Data.Unit

open import Assembly.Base      𝓥 A
open import Assembly.Trackable 𝓥 A
open PcaStr (str A)

⊥ : Asm₀
⊥ = Empty , asmstr _⊩⊥_ (_isRealisable)
  where
    _⊩⊥_ : ⟨ A ⟩ → Empty → 𝓤 ̇
    a ⊩⊥ ()

    _isRealisable : (x : Empty) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩⊥ x)
    () isRealisable

□_ : Asm 𝓤 → Asm 𝓤
□ (|X| , asmstr _⊩_ _) = |□X| , asmstr _⊩□x_ _isRealisable
  where
    |□X| = Σ[ a ∈ ⟨ A ⟩ ] Σ[ x ∈ |X| ] (a ⊩ x)

    _⊩□x_   : ⟨ A ⟩ → |□X| → universeOf |X| ̇
    a ⊩□x (a′ , x , a′⊩x) = Lift (a ≡ a′)

    _isRealisable  : (x : |□X|) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩□x x)
    (a , x , a⊩x) isRealisable = ∣ a , lift refl ∣

∇₀_ : (X : 𝓤 ̇) → Asm 𝓤
∇₀ X = X , asmstr (λ a x → Unit*) λ x → {! nonEmpty !}
  where
    open IsPCA isPCA
