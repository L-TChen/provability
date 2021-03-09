{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.S4 where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub)
open import Later

open import Calculus.Untyped
  hiding (Z)
  
open import Assembly.Base
open import Assembly.Properties
open import Assembly.Exposure

private
  variable
    X Y Z : Asm 𝓤

module _ (Q : Quoting) where
  open Quoting Q

  □_ : Asm 𝓤 → Asm 𝓤
  □_ {𝓤} (|X| , _⊩_ , ⊩-is-realisability) = |□X| , _⊩□X_ , record
    { ⊩-respects-↠ = λ {x} {x′} {y} → ⊩□X-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩□X-right-total
    }
    where
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ x ꞉ |X| ] M ⊩ x
      -- Can we remove truncation? If so, is □id still equal to id? 
      -- Ans. If we assume that ⫣ is a mere proposition, then ▹[ α ] (...) is also a mere proposition (▹isProp→isProp▹).
      -- Therefore, we don't need propositional truncation here.

      _⊩□X_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩□X (M , _ , _) = Lift (n̅ -↠ ⌜ M ⌝)

      ⊩□X-respect-↠ : _⊩□X_ respects _-↠_ on-the-left
      ⊩□X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩□X-right-total :  _⊩□X_ IsRightTotal
      ⊩□X-right-total (M , _ , M⫣x) = ∣ ⌜ M ⌝ , lift (⌜ M ⌝ _-↠_.∎) ∣

  □map₀ : Trackable X Y → ⟨ □ X ⟩ → ⟨ □ Y ⟩
  □map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ] , f x , F⊩f M⊩x

  □map₁ : Λ₁ → Λ₁
  □map₁ F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {𝓤} {X} {Y} Ff@(f , F , f⫣F) = □map₀ Ff , □map₁ F , 
    λ {M} {x} → □F⊩□f {M} {x}
    where
      open -↠-Reasoning
      □F⊩□f : Tracks (□ X) (□ Y) (□map₁ F) (□map₀ Ff)
      □F⊩□f {n̅} {M , _ , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  □id=id : (X : Asm 𝓤) → (x : ⟨ □ X ⟩) → □map₀ (id X) x ≡ x
  □id=id X x = refl

  □-isExposure : IsExposure {𝓤} □_  □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = □reflects∼
    }
    where 
      postulate
      -- Use cubical argument to prove this.
        □gf=□g□f : (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ □ X ⟩) → □map₀ (g ∘ f) x ≡ □map₀ g (□map₀ f x)
        ↑ₗ-injective : {Γ Δ : Cxt} {A : 𝕋} {M N : Δ ⊢ A} → ↑ₗ_ {Δ} {_} {Γ} M ≡ ↑ₗ N → M ≡ N

      □F=□G→F=G : (F G : Λ₁) → □map₁ F ≡ □map₁ G → F ≡ G
      □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decode (encode □F=□G .fst .snd)))

      postulate
        □reflects∼ : (f g : Trackable X Y)
          → □map f ∼ □map g ꞉ □ X →ₐ □ Y
          → f ∼ g ꞉ X →ₐ Y

  □-exposure : Exposure 𝓤
  □-exposure = exposure □_ □map □-isExposure

  eval : Trackable (□ X) X
  eval {X = X} = (λ x → fst (snd x)) , E ,
    λ { {N} {M , x , M⊩x} N-↠⌜M⌝ →
      X.⊩-respects-↠ (reduce-ssubst E (lower N-↠⌜M⌝)) ((X.⊩-respects-↠ (E-↠ M) M⊩x)) }
    where
      module X  = AsmStr (str X)
      module □X = AsmStr (str (□ X))
      postulate
        E : Λ₁ 
        E-↠ : ∀ M → E [ ⌜ M ⌝ ] -↠ M

  quoting-does-not-exist : (q : NaturalTransformation {𝓤₀} Id □-exposure) → ⊥
  quoting-does-not-exist (fun , naturality) = quoting-not-definable (QΛ , QΛ-is-quoting)
    where
      qQ-at-Λ : Trackable Λ₀ₐ (□ Λ₀ₐ)
      qQ-at-Λ = fun

      qΛ : Λ₀ → Σ[ N ꞉ Λ₀ ] Σ[ M ꞉ Λ₀ ] N -↠ M
      qΛ = qQ-at-Λ .fst

      QΛ : Λ₁
      QΛ = HasTracker.F (qQ-at-Λ .snd)

      qQ-at-⊤ : Trackable ⊤ₐ (□ ⊤ₐ)
      qQ-at-⊤ = fun

      □*→Λ-is-constant : ∀ (M : Λ₀) x → □map (*→Λ M) .fst x ≡ (M , M , -↠-refl)
      □*→Λ-is-constant M x = begin
        □map (*→Λ M) .fst x
          ≡⟨ refl ⟩
        ↑₁ M [ _ ] , M , _
          ≡⟨ cong₂ {C = λ _ _ → ⟨ □ Λ₀ₐ ⟩} (λ L N → (L , M , N)) (subst-rename-∅ _ M) {!!} ⟩
        M , M , -↠-refl ∎
        where open ≡-Reasoning

      natural-on-*→Λ : (M : Λ₀) → qQ-at-Λ ∘ *→Λ M ∼ □map (*→Λ M) ∘ qQ-at-⊤ ꞉ ⊤ₐ →ₐ □ Λ₀ₐ
      natural-on-*→Λ M = naturality (*→Λ M)

      lem : (M : Λ₀) → qΛ M ≡ (M , M , -↠-refl)
      lem M = begin
        qΛ M
          ≡⟨ refl ⟩
        qΛ (*→Λ M .fst _)
          ≡⟨ natural-on-*→Λ M _ ⟩
        □map (*→Λ M) .fst (qQ-at-⊤ .fst _)
          ≡⟨ □*→Λ-is-constant M (qQ-at-⊤ .fst _) ⟩
        (M , M , -↠-refl) ∎
        where open ≡-Reasoning
        
      QΛ[M] : {N M : Λ₀} → N -↠ M → Lift (QΛ [ N ] -↠ ⌜ qΛ M .fst ⌝)
      QΛ[M] = HasTracker.F⊩f (qQ-at-Λ .snd) 

      QΛ-is-quoting : (M : Λ₀) → QΛ [ M ] -↠ ⌜ M ⌝
      QΛ-is-quoting M = begin
        QΛ [ M ]
          -↠⟨ lower (QΛ[M] -↠-refl) ⟩
        ⌜ qΛ M .fst ⌝
        ≡[ i ]⟨ ⌜ lem M i .fst  ⌝ ⟩
        ⌜ M ⌝ ∎
        where open -↠-Reasoning
