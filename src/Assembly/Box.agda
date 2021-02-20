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

  □_ : Asm 𝓤 → Asm 𝓤
  □_ {𝓤} (|X| , _⫣_ , ⫣-is-realisability) = |□X| , _⫣□X_ , record
    { ⫣-respects-↠ = λ {x} {x′} {y} → ⫣□X-respect-↠ {x} {x′} {y}
    ; ⫣-left-total = ⫣□X-left-total
    }
    where
      |□X| : 𝓤 ̇
      |□X| = Σ[ ▹x ꞉ ▹ |X| ] Σ[ M ꞉ Λ₀ ] ▹[ α ] ▹x α ⫣ M 
      -- Can we remove truncation? If so, is □id still equal to id? 
      -- Ans. If we assume that ⫣ is a mere proposition, then ▹[ α ] (...) is also a mere proposition (▹isProp→isProp▹).
      -- Therefore, we don't need propositional truncation here.

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
      open -↠-Reasoning
      □F⊩□f : Tracks (□ X) (□ Y) (□map₁ F) (□map₀ Ff)
      □F⊩□f {n̅} {_ , M , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  □id=id : (X : Asm 𝓤) → (x : ⟨ □ X ⟩) → □map₀ (id {X = X}) x ≡ x
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
      -- □gf=□g□f (g , G , G⊩g) (f , F , F⊩f) i (M , ▹x , ▹M⊩x) = {!!} , (λ α → g (f (▹x α))) , {!!}
        □gf=□g□f : (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ □ X ⟩) → □map₀ (g ∘ f) x ≡ □map₀ g (□map₀ f x)
        ↑ₗ-injective : {Γ Δ : Cxt} {A : 𝕋} {M N : Δ ⊢ A} → ↑ₗ_ {Δ} {_} {Γ} M ≡ ↑ₗ N → M ≡ N

      □F=□G→F=G : (F G : Λ₁) → □map₁ F ≡ □map₁ G → F ≡ G
      □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decode (encode □F=□G .fst .snd)))

      postulate
        -- this is required to prove `□reflects∼`
        ▹map-injective : {X Y : 𝓤 ̇} → (f g : X → Y) → ▹map f ≡ ▹map g → f ≡ g

        □reflects∼ : (f g : Trackable X Y)
          → □map f ∼ □map g ꞉ □ X →ₐ □ Y
          → f ∼ g ꞉ X →ₐ Y

  □-exposure : Exposure 𝓤
  □-exposure = exposure □_ □map □-isExposure

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (▹x , 𝑰 , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- Show that there is no natural transformation I ⇒ □.
  Λ₀ₐ : Asm 𝓤₀
  Λ₀ₐ = Λ₀ , (λ M N → N -↠ M) , record
    { ⫣-respects-↠ = -↠-trans
    ; ⫣-left-total = λ M → ∣ M , -↠-refl ∣
    }

  Λ-singleton : Λ₀ → Asm 𝓤₀
  Λ-singleton M = Unit , (λ _ N → N -↠ M) , record
    { ⫣-respects-↠ = -↠-trans
    ; ⫣-left-total = λ _ → ∣ M , -↠-refl ∣
    }

  *→Λ : (M : Λ₀) → Trackable (Λ-singleton M) Λ₀ₐ
  *→Λ M = (λ _ → M) , ↑₁ M , λ {N} N-↠M → begin
    ↑₁ M [ N ]
      ≡⟨ subst-rename-∅ _ M ⟩
    M
      -↠⟨ -↠-refl ⟩
    M ∎
    where open -↠-Reasoning

  □*→Λ : (M : Λ₀) → Trackable (□ Λ-singleton M) (□ Λ₀ₐ)
  □*→Λ M = □map (*→Λ M)
  
  quoting-does-not-exist : (q : NaturalTransformation {𝓤₀} Id □-exposure) → ⊥
  quoting-does-not-exist (fun , naturality) = quoting-not-definable (QΛ , QΛ-is-quoting)
    where
      qQ-at-Λ : Trackable Λ₀ₐ (□ Λ₀ₐ)
      qQ-at-Λ = fun {X = Λ₀ₐ}

      qQ-at- : (M : Λ₀) → Trackable (Λ-singleton M) (□ Λ-singleton M)
      qQ-at- M = fun {X = Λ-singleton M}

      qM : (M : Λ₀) → Unit → Σ[ ▹x ꞉ ▹ Unit ] Σ[ N ꞉ Λ₀ ] ▹ N -↠ M
      qM M = qQ-at- M .fst

      qΛ : Λ₀ → Σ[ ▹M ꞉ ▹ Λ₀ ] Σ[ N ꞉ Λ₀ ] ▹[ α ] N -↠ ▹M α
      qΛ = qQ-at-Λ .fst

      QΛ : Λ₁
      QΛ = HasTracker.F (qQ-at-Λ .snd)

      □*→Λ-is-constant : ∀ (M : Λ₀) x → (□*→Λ M) .fst x ≡ (next M , M , λ _ → -↠-refl)
      □*→Λ-is-constant M x = begin
        (□*→Λ M) .fst x
          ≡⟨ refl ⟩
        next M , ↑₁ M [ _ ] , _
          ≡⟨ {!!} ⟩
        next M , M , {!!}
          ≡⟨ {!!} ⟩
        (next M , M , λ _ → -↠-refl) ∎
        where open ≡-Reasoning

      natural-on-*→Λ : (M : Λ₀) → qQ-at-Λ ∘ *→Λ M ∼ □map (*→Λ M) ∘ qQ-at- M ꞉ Λ-singleton M →ₐ □ Λ₀ₐ
      natural-on-*→Λ M = naturality (*→Λ M)

      lem1 : (M : Λ₀) → qΛ M ≡ (next M , M , λ _ → -↠-refl)
      lem1 M = begin
        (qQ-at-Λ .fst) M
          ≡⟨ refl ⟩
        (qQ-at-Λ .fst) (*→Λ M .fst tt)
          ≡⟨ natural-on-*→Λ M tt ⟩
        (□*→Λ M) .fst (qQ-at- M .fst tt)
          ≡⟨ □*→Λ-is-constant M (qQ-at- M .fst tt) ⟩
        (next M , M , λ _ → -↠-refl) ∎
        where open ≡-Reasoning
        
      QΛ[M] : {N M : Λ₀} → N -↠ M → Lift (QΛ [ N ] -↠ ⌜ qΛ M .snd .fst ⌝)
      QΛ[M] =  HasTracker.F⫣f (qQ-at-Λ .snd) 

      QΛ-is-quoting : (M : Λ₀) → QΛ [ M ] -↠ ⌜ M ⌝
      QΛ-is-quoting M = begin
        QΛ [ M ]
          -↠⟨ lower (QΛ[M] -↠-refl) ⟩
        ⌜ fst (snd (qΛ M)) ⌝
          ≡[ i ]⟨ ⌜ fst (snd (lem1 M i) ) ⌝ ⟩
        ⌜ M ⌝ ∎
        where open -↠-Reasoning
