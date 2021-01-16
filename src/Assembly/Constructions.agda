{-# OPTIONS --without-K --cubical #-}

open import Prelude
open import Cubical.Data.Empty
  renaming (⊥ to Empty)

open import Algebra.PCA

module Assembly.Constructions (A : PCA 𝓤₀) where

open import Assembly.Base      A
--open import Assembly.Trackable A
open PcaStr (str A)

⊥ : Asm₀
⊥ = Empty , asmstr _⊩⊥_ (_isRealisable)
  where
    _⊩⊥_ : ⟨ A ⟩ → Empty → 𝓤 ̇
    a ⊩⊥ ()

    _isRealisable : (x : Empty) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩⊥ x)
    () isRealisable

□_ : Asm 𝓤 → Asm 𝓤
□ (|X| , asmstr _⊩_ _isRealisable-in-|X|) = |□X| , asmstr _⊩□x_ _isRealisable
  where
    |□X| = Σ[ a ∈ ⟨ A ⟩ ] Σ[ x ∈ |X| ] (a ⊩ x)

    _⊩□x_   : ⟨ A ⟩ → |□X| → universeOf |X| ̇
    a ⊩□x (a′ , x , a′⊩x) = Lift (a ≡ a′)

    _isRealisable  : (x : |□X|) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩□x x)
    (a , x , a⊩x) isRealisable = ∣ a , lift refl ∣
