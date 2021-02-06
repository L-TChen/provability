{-# OPTIONS --without-K --cubical #-}


module Assembly.Exposure where

open import Prelude
  hiding (id; _∘_)
open import Calculus.SystemT
open import Assembly.Base

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Endo-exposure

record IsEndoExposure (Q : Asm 𝓤 → Asm 𝓤) : 𝓤 ⁺ ̇ where 
  constructor is-exposure
  field
    map           : Trackable X Y → Trackable (Q X) (Q Y)
    preserve-id   : map id ∼ id ꞉ Q X →ₐ Q X
    preserve-comp : {f : Trackable X Y} {g : Trackable Y Z}
      → map g ∘ map f ∼ map (g ∘ f) ꞉ Q X →ₐ Q Z
    reflects-∼    : {f g : Trackable X Y}
      → map f ∼ map g ꞉ Q X →ₐ Q Y
      →     f ∼ g     ꞉ X   →ₐ Y

record EndoExposure : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    Q          : Asm 𝓤 → Asm 𝓤
    isExposure : IsEndoExposure Q
    
module _ (Q : Quoting) where
  open Quoting Q

  □_ : Asm 𝓤 → Asm 𝓤
  □ (|X| , asmstr A _⊩_ _isRealisableₓ) = |□X| , asmstr nat _⊩□x_  _isRealisable
    where
    -- □ X consists of terms of type `nat` which reduces to a literal
    -- of a Gödel numbering, this reflects the fact that a well-typed
    -- metaprogram may produce a representation containing β-redexs.
      |□X| : (universe-of |X|) ̇
      |□X| = Σ[ n̅ ꞉ Prog nat ] Σ[ ▹x ꞉ ▹ |X| ] ▹[ α ] ∃[ M ꞉ Prog A ] n̅ -↠ ⌜ M ⌝ × M ⊩ ▹x α

      _⊩□x_   : Prog nat → |□X| → _
      N ⊩□x (M , x , M⊩x) = Lift (N -↠ M)

      _isRealisable  : Π[ x ꞉ |□X| ] ∃[ M ꞉ Prog nat ] M ⊩□x x
      (M , x , M⊩x) isRealisable = ∣ M , lift -↠-refl ∣

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (zero , ▹x ,
    λ α → ⊥*-elim {A = ∃[ M ꞉ Prog `⊥ ] zero -↠ ⌜ M ⌝ × M ⊩⊥ ▹x α } (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
