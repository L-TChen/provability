{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.GL where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub; r)
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
  □_ {𝓤} X = |□X| , _⊩_ , record
    { ⊩-respects-↠ = λ {x} {x′} {y} → ⊩-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩-right-total
    }
    where
      module X = AsmStr (str X)
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ ▹x ꞉ ▹ ⟨ X ⟩ ] ▹[ α ] (M X.⊩ ▹x α)
      -- Can we remove truncation? If so, is □id still equal to id? 
      -- Ans. If we assume that ⫣ is a mere proposition, then ▹[ α ] (...) is also a mere proposition (▹isProp→isProp▹).
      -- Therefore, we don't need propositional truncation here.

      _⊩_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩ (M , ▹x , ▹x⫣M)= Lift (n̅ -↠ ⌜ M ⌝)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , ▹x , M⫣x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map₀ : Trackable X Y → ⟨ □ X ⟩ → ⟨ □ Y ⟩
  □map₀ (f , F , F⊩f) (M , ▹x , M⊩x) = F [ M ] , ▹map f ▹x , λ α → F⊩f (M⊩x α)

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
  □id=id X x =  refl

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
        -- this is required to prove `□reflects∼`, but unfortunately we canno't have this verified in the model. 
        ▹map-injective : {X Y : 𝓤 ̇} → (f g : X → Y) → ▹map f ≡ ▹map g → f ≡ g

        □reflects∼ : (f g : Trackable X Y)
          → □map f ∼ □map g ꞉ □ X →ₐ □ Y
          → f ∼ g ꞉ X →ₐ Y

  □-exposure : Exposure 𝓤
  □-exposure = exposure □_ □map □-isExposure

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- Lemma: □ sends constant maps to constant maps
  -- The proof is clear.x
  -- Theorem: There is no natural transformation q : I ⇒ □.
  -- Proof sketch: By naturality, qΛ is determined by its component at the terminal object ⊤ₐ. 
  -- 
  quoting-does-not-exist : (q : NaturalTransformation {𝓤₀} Id □-exposure) → ⊥
  quoting-does-not-exist (fun , naturality) = quoting-not-definable (QΛ , QΛ-is-quoting)
    where
      qQ-at-Λ : Trackable Λ₀ₐ (□ Λ₀ₐ)
      qQ-at-Λ = fun

      qΛ : Λ₀ → Σ[ N ꞉ Λ₀ ] Σ[ ▹M ꞉ ▹ Λ₀ ] ▹[ α ] N -↠ ▹M α
      qΛ = qQ-at-Λ .fst

      QΛ : Λ₁
      QΛ = HasTracker.F (qQ-at-Λ .snd)

      qQ-at-⊤ : Trackable ⊤ₐ (□ ⊤ₐ)
      qQ-at-⊤ = fun

      □*→Λ-is-constant : ∀ (M : Λ₀) x → □map (*→Λ M) .fst x ≡ (M , next M , λ _ → -↠-refl)
      □*→Λ-is-constant M x = begin
        □map (*→Λ M) .fst x
          ≡⟨ refl ⟩
        ↑₁ M [ _ ] , next M , _
          ≡⟨ cong₂ {C = λ _ _ → ⟨ □ Λ₀ₐ ⟩} (λ L N → (L , next M , N)) (subst-rename-∅ _ M) {!!} ⟩
        M , next M , (λ _ → -↠-refl) ∎
        where open ≡-Reasoning

      natural-on-*→Λ : (M : Λ₀) → qQ-at-Λ ∘ *→Λ M ∼ □map (*→Λ M) ∘ qQ-at-⊤ ꞉ ⊤ₐ →ₐ □ Λ₀ₐ
      natural-on-*→Λ M = naturality (*→Λ M)

      lem : (M : Λ₀) → qΛ M ≡ (M , next M , λ _ → -↠-refl)
      lem M = begin
        qΛ M
          ≡⟨ refl ⟩
        qΛ (*→Λ M .fst _)
          ≡⟨ natural-on-*→Λ M _ ⟩
        □map (*→Λ M) .fst (qQ-at-⊤ .fst _)
          ≡⟨ □*→Λ-is-constant M (qQ-at-⊤ .fst _) ⟩
        (M , next M , λ _ → -↠-refl) ∎
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

  GL₀ : {X : Asm 𝓤} → ⟨ □ (□ X ⇒ X) ⟩ → ⟨ □ X ⟩
  GL₀ {X = X@(|X| , _⊩_ , ⊩-is-realisability)} (F , ▹f , ▹F⊩f) = F · ⌜ gfix F ⌝ , ▹Σ
    (r λ α → ▹f α .fst , λ ▹M⊩x n̅-↠⌜M⌝ → ▹F⊩f α (lift n̅-↠⌜M⌝))
      where
        open IsRealisability ⊩-is-realisability
        module □X   = AsmStr (str (□ X))
        module □X⇒X = AsmStr (str (□ X ⇒ X))
        r : ▹ (Σ[ f ꞉ (⟨ □ X ⟩ → ⟨ X ⟩) ]
            ({n̅ M : Λ₀} {▹x : ▹ ⟨ X ⟩} (▹M⊩x : ▹[ α ] M ⊩ ▹x α) → n̅ -↠ ⌜ M ⌝ → (F · n̅) ⊩ f (M , ▹x , ▹M⊩x)))
          → ▹ (Σ[ x ꞉ ⟨ X ⟩ ] (F · ⌜ gfix F ⌝) ⊩ x)
        r ▹hyp α = fix λ ▹x →
            f (gfix F , (λ β → ▹x β .fst) , λ β → ⊩-respects-↠ gfix-↠ (▹x β .snd)) ,
            F⊩f (λ β → ⊩-respects-↠ gfix-↠ (▹x β .snd)) -↠-refl
          where
            f   = ▹hyp α .fst
            F⊩f = ▹hyp α .snd

  GL : {X : Asm 𝓤}
    → Trackable (□ X) X
    → ⟨ □ X ⟩
  GL {X = X} (f , F , f⫣F) = F [ ⌜ gfix {!!} ⌝ ] , {!!}
    where
      module X = AsmStr (str X)
        

  -- GL : Trackable (□ (□ X ⇒ X)) → □ X
  -- GL = GL₀ , {!!} , {!!}
  
