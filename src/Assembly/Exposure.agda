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
  open -↠-Reasoning

  □_ : Asm 𝓤 → Asm 𝓤
  □_ {𝓤} X@(|X| , ⊩ , is⊩ ⊩-respect-↠ ⊩-right-total) = |□X| , ⊩□X , is⊩ ⊩□X-respect-↠ ⊩□X-right-total
    where
      module X = AsmStr (str X)
      |□X| : 𝓤 ̇
      |□X| = Σ[ A ꞉ 𝕋 ] Σ[ M ꞉ Prog A ] Σ[ ▹x ꞉ ▹ |X| ] ▹[ α ] M X.⊩ ▹x α ⦂ A

      ⊩□X  : (A : 𝕋) → (M : Prog A) → |□X| → 𝓤 ̇
      ⊩□X nat n̅ (A , M , ▹x , M⊩▹x) = Lift (n̅ -↠ ⌜ M ⌝)
      ⊩□X _   _ _                   = ⊥*

      ⊩□X-respect-↠ : {A : 𝕋} {M N : Prog A} {x : |□X|}
        → M -↠ N → ⊩□X A N x → ⊩□X A M x
      ⊩□X-respect-↠ {A = nat}     M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      ⊩□X-respect-↠ {A = `⊤}      M-↠N ()
      ⊩□X-respect-↠ {A = `⊥}      M-↠N ()
      ⊩□X-respect-↠ {A = A `× A₁} M-↠N ()
      ⊩□X-respect-↠ {A = A `→ A₁} M-↠N ()
      
      ⊩□X-right-total : (x : |□X|) → ∃[ A ꞉ 𝕋 ] Σ[ M ꞉ Prog A ] ⊩□X A M x
      ⊩□X-right-total (A , M , ▹x , M⊩x) = ∣ nat , ⌜ M ⌝ , lift -↠-refl ∣

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {𝓤} {X} {Y} (f , hastracker T F F⊩f) = □f , hastracker (λ _ → nat) {!!} {!!} -- □F □F⊩□f
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)
      module □X = AsmStr (str (□ X))
      module □Y = AsmStr (str (□ Y))
      □f : ⟨ □ X ⟩ → ⟨ □ Y ⟩
      □f (A , M , ▹x , M⊩x) = T A , F [ M ] , ▹map f ▹x , λ α → F⊩f (M⊩x α) 

      □F : ∀ {A} → A , ∅ ⊢ nat
      □F = {!!}

      □F⊩□f : Tracks (□ X) (□ Y) □F □f
      □F⊩□f {nat} {n̅} {A , M , ▹x , M⊩x}    (lift n̅-↠⌜M⌝) = {!!}
     -- lift (begin
     --   ↑₁ Ap [ n̅ ] · ↑₁ ⌜ {!!} ⌝ [ n̅ ] · n̅
     --     -↠⟨ {!!} ⟩
     --   ⌜ F [ M ] ⌝ ∎)

      -- 1. n̅ -↠ ⌜ M ⌝ by assumption
      -- ⌜ (ƛ F) · M ⌝ -↠ ⌜ F [ M ] ⌝
      -- Ap · ⌜ ƛ F ⌝ · n̅ -↠ ⌜ F [ M ] ⌝ by
      -- Ap · ⌜ ƛ F ⌝ · n̅ -↠ Ap · ⌜ ƛ F ⌝ · ⌜ M ⌝ -↠ ⌜ (ƛ F) · M ⌝ -↠ ⌜ F [ M ] ⌝

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (nat , `zero , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- -- quoting-does-not-exist = {!!}
