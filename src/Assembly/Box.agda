{-# OPTIONS --without-K --cubical #-}


module Assembly.Box where

open import Prelude

open import Calculus.SystemT
  hiding (⟨_,_⟩; _,_)
open import Assembly.Base

module _ (Q : Quoting) where
  open Quoting Q

  □_ : Asm 𝓤₀ → Asm 𝓤₀
  □ (|X| , asmstr A _⊩_ _isRealisableₓ) = |□X| , asmstr nat _⊩□x_ _isRealisable
    where
      |□X| : (universe-of |X|) ̇
      |□X| = Σ[ n̅ ꞉ Prog nat ] Σ[ ▹x ꞉ ▹ |X| ] ∃[ M ꞉ Prog A ] (n̅ -↠ ⌜ M ⌝) × (▹[ α ] M ⊩ ▹x α) 

      _⊩□x_   : Prog nat → |□X| → _
      b ⊩□x (a , x , a⊩x) = Lift (a ≡ b)

      _isRealisable  : Π[ x ꞉ |□X| ] ∃[ a ꞉ Prog nat ] a ⊩□x x
      (a , x , a⊩x) isRealisable = ∣ a , lift refl ∣

  module _ where
    open Mor (□ ⊥ₐ) ⊥ₐ
    
    -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
    bang : (⟨ □ ⊥ₐ ⟩ → ⊥) → ▹ ⊥ → ⊥
    bang eval⊥ ▹x = eval⊥ (⌜ ⟨⟩ ⌝ , ▹x , ∣ ⟨⟩ , (⌜ ⟨⟩ ⌝ _-↠_.∎) , (λ α → ⊥-elim {𝓤₀} {λ ()} (▹x α)) ∣)

    -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
    eval-does-not-exist : Π[ e ꞉ (⟨ □ ⊥ₐ ⟩ → ⟨ ⊥ₐ ⟩) ] Π[ r ꞉ Prog (nat →̇ ⊤̇) ] (r tracks e → ⊥)
    eval-does-not-exist e _ _ = fix (bang e)

  module _ where
    open Mor ⊥ₐ (□ ⊥ₐ)
--    quoting-does-not-exist : Π[ q : ⟨ X ⟩ → ⟨ □ X ⟩ ] 
