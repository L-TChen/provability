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
  □_ {𝓤} X = |□X| , _⫣□X_ , record
    { ⫣-respects-↠ = λ {x} {x′} {y} → ⫣□X-respect-↠ {x} {x′} {y}
    ; ⫣-left-total = ⫣□X-left-total }
    where
      module X = AsmStr (str X)
      |□X| : 𝓤 ̇
      |□X| = Σ[ ▹x ꞉ ▹ ⟨ X ⟩ ] Σ[ M ꞉ Λ₀ ] ▹[ α ] ▹x α X.⫣ M 
      -- can we remove truncation? If so, is □id still equal to id? 

      _⫣□X_ : |□X| → (M : Λ₀) → 𝓤 ̇
      (▹x , M , ▹x⫣M) ⫣□X n̅ = Lift (n̅ -↠ ⌜ M ⌝)

      ⫣□X-respect-↠ : _⫣□X_ respects _-↠_ on-the-right
      ⫣□X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⫣□X-left-total :  _⫣□X_ IsLeftTotal
      ⫣□X-left-total (▹x , M , M⫣x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map₀ : Trackable X Y → ⟨ □ X ⟩ → ⟨ □ Y ⟩
  □map₀ (f , F , f⫣F) (▹x , M , x⫣M) = ▹map f ▹x , F [ M ] , λ α → f⫣F (x⫣M α)

  □map₁ : Λ₁ → Λ₁
  □map₁ F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {𝓤} {X} {Y} Ff@(f , F , f⫣F) = □map₀ Ff , □map₁ F , 
    λ {M} {x} → □F⊩□f {M} {x}
    where
      □F⊩□f : Tracks (□ X) (□ Y) (□map₁ F) (□map₀ Ff)
      □F⊩□f {n̅} {_ , M , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  □id=id : (X : Asm 𝓤) → □map₀ (id {X = X}) ≡ 𝓤.id
  □id=id X = refl
  

  □-isExposure : IsExposure {𝓤} □_  □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = □reflects∼
    }
    where 
      postulate
      -- Use cubical argument to prove this.
      -- □gf=□g□f (g , G , G⊩g) (f , F , F⊩f) i (M , ▹x , ▹M⊩x) = {!!} , (λ α → g (f (▹x α))) , {!!}
        □gf=□g□f : (f : Trackable X Y) (g : Trackable Y Z) → □map₀ (g ∘ f) ≡ □map₀ g 𝓤.∘ □map₀ f
        ↑ₗ-injective : {Γ Δ : Cxt} {A : 𝕋} {M N : Δ ⊢ A} → ↑ₗ_ {Δ} {_} {Γ} M ≡ ↑ₗ N → M ≡ N

      □F=□G→F=G : (F G : Λ₁) → □map₁ F ≡ □map₁ G → F ≡ G
      □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decode (encode □F=□G .fst .snd)))

      □reflects∼ : (f g : Trackable X Y)
        → □map f ∼ □map g ꞉ □ X →ₐ □ Y
        → f ∼ g ꞉ X →ₐ Y
        -- is ▹ : 𝓤 ̇ → 𝓤 ̇ a faithful functor?
      □reflects∼ f g □f=□g = {!!}

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (▹x , 𝑰 , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
