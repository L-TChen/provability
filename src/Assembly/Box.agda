{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.Box where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub)
open import Later

open import Calculus.Untyped
  hiding (Z)
open import Assembly.Base
open import Assembly.Exposure

private
  variable
    X Y Z : Asm 𝓤

module _ (Q : Quoting) where
  open Quoting Q
  open -↠-Reasoning

  □_ : Asm 𝓤 → Asm 𝓤
  □_ {𝓤} X = |□X| , _⊩□X_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩□X-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩□X-right-total }
    where
      module X = AsmStr (str X)
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ ▹x ꞉ ▹ ⟨ X ⟩ ] ▹[ α ] M X.⊩ ▹x α
      -- can we remove truncation? If so, is □id still equal to id? 

      _⊩□X_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩□X (M , ▹x , M⊩▹x) = Lift (n̅ -↠ ⌜ M ⌝)

      ⊩□X-respect-↠ : _⊩□X_ respects _-↠_ on-the-left
      ⊩□X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩□X-right-total : IsRightTotal _⊩□X_
      ⊩□X-right-total (M , ▹x , M⊩x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map₀ : Trackable X Y → ⟨ □ X ⟩ → ⟨ □ Y ⟩
  □map₀ (f , F , F⊩f) (M , ▹x , M⊩x) = F [ M ] , ▹map f ▹x , λ α → F⊩f (M⊩x α)

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {𝓤} {X} {Y} Ff@(f , F , F⊩f) = □map₀ Ff , □F , 
    λ {M} {x} → □F⊩□f {M} {x}
    where
      □F : ⋆ , ∅ ⊢ ⋆
      □F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

      □F⊩□f : Tracks (□ X) (□ Y) □F (□map₀ Ff)
      □F⊩□f {n̅} {M , _ , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  □id=id : (X : Asm 𝓤) → □map₀ (id {X = X}) ≡ 𝓤.id
  □id=id X i (M , x , M⊩x) = M , x , M⊩x

  -- Use cubical argument to prove this.
  postulate
    □gf=□g□f : (f : Trackable X Y) (g : Trackable Y Z) → □map₀ (g ∘ f) ≡ □map₀ g 𝓤.∘ □map₀ f
  -- □gf=□g□f (g , G , G⊩g) (f , F , F⊩f) i (M , ▹x , ▹M⊩x) = {!!} , (λ α → g (f (▹x α))) , {!!}

  □reflects∼ : (f g : Trackable X Y)
    → □map f ∼ □map g ꞉ □ X →ₐ □ Y
    → f ∼ g ꞉ X →ₐ Y
    -- is ▹ : 𝓤 ̇ → 𝓤 ̇ a faithful functor?
  □reflects∼ f g □f=□g = {!!}

  □-isExposure : IsExposure {𝓤} □_  □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = □reflects∼
    }

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
