{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.Exposure where

open import Prelude
  hiding (id; _∘_; Sub)
open import Calculus.Untyped
  hiding (Z)
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
  □_ {𝓤} (|X| , _⊩_ , ⊩-realisability) = |□X| , _⊩□X_ ,
    is⊩ (λ {x} {x′} {y} → ⊩□X-respect-↠ {x} {x′} {y}) ⊩□X-right-total
    where
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ ▹x ꞉ ▹ |X| ] ▹[ α ] M ⊩ ▹x α
      -- can we remove truncation? If so, is □id still equal to id? 

      _⊩□X_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩□X (M , ▹x , M⊩▹x) = Lift (n̅ -↠ ⌜ M ⌝)

      ⊩□X-respect-↠ : _⊩□X_ respects _-↠_ on-the-left
      ⊩□X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩□X-right-total : IsRightTotal _⊩□X_
      ⊩□X-right-total (M , ▹x , M⊩x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {𝓤} {X} {Y} (f , F , F⊩f) = □f , □F , 
    λ {M} {x} → □F⊩□f {M} {x}
    where
      □f : ⟨ □ X ⟩ → ⟨ □ Y ⟩
      □f (M , ▹x , M⊩x) = F [ M ] , ▹map f ▹x , λ α → F⊩f (M⊩x α)

      □F : ⋆ , ∅ ⊢ ⋆
      □F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

      □F⊩□f : Tracks (□ X) (□ Y) □F □f
      □F⊩□f {n̅} {M , _ , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
