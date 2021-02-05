{-# OPTIONS --without-K --cubical #-}

open import Prelude

module Assembly.Box where

open import Calculus.SystemT
  hiding (⟨_,_⟩; _,_)
open import Assembly.Base

module _ (q : Quoting) where
  open Quoting q

  □_ : Asm 𝓤₀ → Asm 𝓤₀
  □ (|X| , asmstr A _⊩_ _isRealisableₓ) = |□X| , asmstr nat _⊩□x_ _isRealisable
    where
      |□X| : (universe-of |X|) ̇
      |□X| = Σ[ a ꞉ Prog nat ] Σ[ ▹x ꞉ ▹ |X| ] Σ[ M ꞉ Prog A ] (⌜ M ⌝ ≡ a) × (▹[ α ] M ⊩ ▹x α) 

      _⊩□x_   : Prog nat → |□X| → _
      b ⊩□x (a , x , a⊩x) = Lift (a ≡ b)

      _isRealisable  : Π[ x ꞉ |□X| ] ∃[ a ꞉ Prog nat ] a ⊩□x x
      (a , x , a⊩x) isRealisable = ∣ a , lift refl ∣

  open Mor (□ ⊥ₐ) ⊥ₐ
  -- Corollary.
  --   1. Evaluation □ ⊥ → ⊥ does not exist.
  --   2. There is no natural transformation □ → Id of exposures.
  eval-does-not-exist : {A : 𝕋} → Π[ e ꞉ (⟨ □ ⊥ₐ ⟩ → ⊥) ] Π[ r ꞉ Prog (nat →̇ ⊤̇) ] (r tracks e → ⊥)
  eval-does-not-exist e _ _ = fix (lem e)
    where
      -- Lemma. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
      lem : (⟨ □ ⊥ₐ ⟩ → ⊥) → ▹ ⊥ → ⊥
      lem eval⊥ ▹x = bang
        where
          bang : ⊥
          bang = eval⊥ (⌜ ⟨⟩ ⌝ , ▹x , ⟨⟩ , refl , λ α → ⊥-elim {𝓤₀} {A = λ ()} (▹x α)) 
