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

--record IsEndoExposure (Q : Asm 𝓤 → Asm 𝓤) : 𝓤 ⁺ ̇ where 
--  constructor is-exposure
--  field
--    map           : Trackable X Y → Trackable (Q X) (Q Y)
--    preserve-id   : map id ∼ id ꞉ Q X →ₐ Q X
--    preserve-comp : {f : Trackable X Y} {g : Trackable Y Z}
--      → map g ∘ map f ∼ map (g ∘ f) ꞉ Q X →ₐ Q Z
--    reflects-∼    : {f g : Trackable X Y}
--      → map f ∼ map g ꞉ Q X →ₐ Q Y
--      →     f ∼ g     ꞉ X   →ₐ Y
--
--record EndoExposure : 𝓤 ⁺ ̇ where
--  constructor _,_
--  field
--    Q          : Asm 𝓤 → Asm 𝓤
--    isExposure : IsEndoExposure Q
    
module _ (Q : Quoting) where
  open Quoting Q
  open -↠-Reasoning

  □_ : Asm 𝓤 → Asm 𝓤
  □_ {𝓤} (|X| , asmstr A _⊩_ (is⊩ resp total)) = |□X| ,
    asmstr nat _⊩□x_ (is⊩ (λ M-↠N N⊩x → lift (-↠-trans M-↠N (lower N⊩x))) ⊩-right-total)
    where
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Prog A ] Σ[ ▹x ꞉ ▹ |X| ] ∥ ▹[ α ] M ⊩ ▹x α ∥

      _⊩□x_   : Prog nat → |□X| → 𝓤 ̇
      n̅ ⊩□x (M , _ , _) = Lift (n̅ -↠ ⌜ M ⌝)
      
      ⊩-right-total : (x : |□X|) → ∃[ M ꞉ Prog nat ] M ⊩□x x
      ⊩-right-total (M , ▹x , M⊩x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {X = X} {Y = Y} (f , F , F⊩f) = {!!} , {!!} 
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)
      module □X = AsmStr (str (□ X))
      module □Y = AsmStr (str (□ Y))
      □f : ⟨ □ X ⟩ → ⟨ □ Y ⟩
      □f (M , ▹x , p) = {!!}

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (? , ▹x , ∣ (λ α → ⊥*-elim (▹x α)) ∣)

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
