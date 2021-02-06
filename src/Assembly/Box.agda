{-# OPTIONS --without-K --cubical #-}


module Assembly.Box where

open import Prelude
open import Calculus.SystemT
open import Assembly.Base

module _ (Q : Quoting) where
  open Quoting Q

  □_ : Asm 𝓤₀ → Asm 𝓤₀
  □ (|X| , asmstr A _⊩_ _isRealisableₓ) = |□X| , asmstr nat _⊩□x_  _isRealisable
    where
      open -↠-Reasoning
    -- □ X consists of terms of type `nat` which reduces to a literal
    -- of a Gödel numbering, this reflects the fact that a well-typed
    -- metaprogram may produce a representation containing β-redexs.
      |□X| : (universe-of |X|) ̇
      |□X| = Σ[ n̅ ꞉ Prog nat ] Σ[ ▹x ꞉ ▹ |X| ] ▹[ α ] ∃[ M ꞉ Prog A ] n̅ -↠ ⌜ M ⌝ × M ⊩ ▹x α

      _⊩□x_   : Prog nat → |□X| → _
      N ⊩□x (M , x , M⊩x) = N -↠ M

      _isRealisable  : Π[ x ꞉ |□X| ] ∃[ M ꞉ Prog nat ] M ⊩□x x
      (M , x , M⊩x) isRealisable = ∣ M , (M ∎) ∣

  module _ where
    open Mor (□ ⊥ₐ) ⊥ₐ
    open -↠-Reasoning
    
    -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
    bang : (⟨ □ ⊥ₐ ⟩ → ⊥) → ▹ ⊥ → ⊥
    bang eval⊥ ▹x = eval⊥ (zero , ▹x ,
      λ α → ⊥-elim {A = λ _ → ∃[ M ꞉ Prog `⊥ ] zero -↠ ⌜ M ⌝ × M ⊩⊥ ▹x α } (▹x α))

    -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
    eval-does-not-exist : Π[ e ꞉ (⟨ □ ⊥ₐ ⟩ → ⟨ ⊥ₐ ⟩) ] Π[ r ꞉ Prog (nat `→ `⊥) ] (r tracks e → ⊥)
    eval-does-not-exist e _ _ = fix (bang e)

  module _ where
    open Mor ⊥ₐ (□ ⊥ₐ)
--    quoting-does-not-exist : Π[ q : ⟨ X ⟩ → ⟨ □ X ⟩ ] 
