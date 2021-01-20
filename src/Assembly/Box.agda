{-# OPTIONS --without-K --cubical #-}

open import Prelude
  renaming (⊥ to Empty)
open import Algebra.PCA

module Assembly.Box (A : PCA 𝓥 𝓤₀) where
open PcaStr (str A)

open import Assembly.Base      𝓥 A

□_ : Asm 𝓤 → Asm 𝓤
□ (|X| , asmstr _⊩_ _) = |□X| , asmstr _⊩□x_ _isRealisable
  where
    |□X| = Σ[ a ꞉ ⟨ A ⟩ ] Σ[ x▹ ꞉ ▹ |X| ] ▹[ α ] a ⊩ x▹ α

    _⊩□x_   : ⟨ A ⟩ → |□X| → universeOf |X| ̇
    a ⊩□x (a′ , x , a′⊩x) = Lift (a ≡ a′)

    _isRealisable  : Π[ x ꞉ |□X| ] ∃[ a ꞉ ⟨ A ⟩ ] a ⊩□x x
    (a , x , a⊩x) isRealisable = ∣ a , lift refl ∣

module _ where
  open Mor (□ ⊥) ⊥
  f : (⟨ □ ⊥ ⟩ → Empty) → ▹ Empty → Empty
  f eval⊥ ▹x = truncElim (λ _ → isProp⊥) bang nonEmpty
    where
      open IsPCA isPCA
      bang : ⟨ A ⟩ → Empty
      bang a = eval⊥ (a , ▹x , λ α → elim {𝓤₀} {A = (λ ())} (▹x α))

  -- Corollary.
  --   1. Evaluation □ ⊥ → ⊥ does not exist.
  --   2. There is no natural transformation □ → Id of exposures.
  eval-does-not-exist : Π[ e ꞉ (⟨ □ ⊥ ⟩ → Empty) ] Π[ r ꞉ ⟨ A ⟩ ] ((r Tracks e) → Empty)
  eval-does-not-exist e _ _ = fix (lem e)
    where
      -- Lemma. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
      lem : (⟨ □ ⊥ ⟩ → Empty) → ▹ Empty → Empty
      lem eval⊥ ▹x = truncElim (λ _ → isProp⊥) bang nonEmpty
        where
          open IsPCA isPCA
          bang : ⟨ A ⟩ → Empty
          bang a = eval⊥ (a , ▹x , λ α → elim {𝓤₀} {A = (λ ())} (▹x α))
