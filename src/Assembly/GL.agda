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
    k     : Cl

module _ (Q : Quoting) where
  open Quoting Q

  □ : (k : Cl) → Asm 𝓤 → Asm 𝓤
  □ {𝓤} k X = |□X| , _⊩_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩-right-total
    }
    where
      module X = AsmStr (str X)
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ ▹x ꞉ ▹ k ⟨ X ⟩ ] ▹[ α ꞉ k ] ∥ M X.⊩ ▹x α ∥
      -- Can we remove truncation? If so, is □id still equal to id? 
      -- Ans. If we assume that ⫣ is a mere proposition, then ▹[ α ] (...) is also a mere proposition (▹isProp→isProp▹).
      -- Therefore, we don't need propositional truncation here.

      _⊩_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩ (M , _ , _)= Lift (n̅ -↠ ⌜ M ⌝)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , ▹x , M⫣x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map₀ : Trackable X Y → ⟨ □ k X ⟩ → ⟨ □ k Y ⟩
  □map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ] , ▹map f x , λ α → ∥-∥map F⊩f (M⊩x α)

  □map₁ : Λ₁ → Λ₁
  □map₁ F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

  □map : Trackable X Y → Trackable (□ k X) (□ k Y)
  □map {𝓤} {X} {Y} Ff@(f , F , f⫣F) = □map₀ Ff , □map₁ F , 
    λ {M} {x} → □F⊩□f {_} {M} {x}
    where
      open -↠-Reasoning
      □F⊩□f : Tracks (□ k X) (□ k Y) (□map₁ F) (□map₀ Ff)
      □F⊩□f {_} {n̅} {M , _ , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  □id=id : (X : Asm 𝓤) → (x : ⟨ □ k X ⟩) → □map₀ (id X) x ≡ x
  □id=id X (M , x , M⊩x) i = M , x , λ α → propTruncIsProp (∥-∥map (λ x → x) (M⊩x α)) (M⊩x α) i

  □-isExposure : IsExposure {𝓤} (□ k)  □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = {!!} -- □reflects∼
    }
    where 
      postulate
      -- Use cubical argument to prove this.
        □gf=□g□f : (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ □ k X ⟩) → □map₀ (g ∘ f) x ≡ □map₀ g (□map₀ f x)
        ↑ₗ-injective : {Γ Δ : Cxt} {A : 𝕋} {M N : Δ ⊢ A} → ↑ₗ_ {Δ} {_} {Γ} M ≡ ↑ₗ N → M ≡ N

      □F=□G→F=G : (F G : Λ₁) → □map₁ F ≡ □map₁ G → F ≡ G
      □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decode (encode □F=□G .fst .snd)))

      postulate
        -- this is required to prove `□reflects∼`, but unfortunately we canno't have this verified in the model. 
        □reflects∼ : (f g : Trackable X Y)
          → (∀ k → □map f ∼ □map g ꞉ □ k X →ₐ □ k Y)
          → f ∼ g ꞉ X →ₐ Y

  □-exposure : (k : Cl) → Exposure 𝓤
  □-exposure k = exposure (□ k) □map □-isExposure

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ k (⊥ₐ {𝓤}) ⟩ → ⊥* {𝓤}) → ▹ k ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ k ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- Lemma: □ sends constant maps to constant maps
  -- The proof is clear.x
  -- Theorem: There is no natural transformation q : I ⇒ □.
  -- Proof sketch: By naturality, qΛ is determined by its component at the terminal object ⊤ₐ. 
  -- 
  quoting-does-not-exist : (q : NaturalTransformation {𝓤₀} Id (□-exposure k)) → ⊥
  quoting-does-not-exist {k = k} (fun , naturality) = quoting-not-definable (QΛ , QΛ-is-quoting)
    where
      qQ-at-Λ : Trackable Λ₀ₐ (□ k Λ₀ₐ)
      qQ-at-Λ = fun

      qΛ : Λ₀ → Σ[ N ꞉ Λ₀ ] Σ[ ▹M ꞉ ▹ k Λ₀ ] ▹[ α ꞉ k ] ∥ N -↠ ▹M α ∥
      qΛ = qQ-at-Λ .fst

      QΛ : Λ₁
      QΛ = HasTracker.F (qQ-at-Λ .snd)

      qQ-at-⊤ : Trackable ⊤ₐ (□ k ⊤ₐ)
      qQ-at-⊤ = fun

      □*→Λ-is-constant : ∀ (M : Λ₀) x → □map (*→Λ M) .fst x ≡ (M , next M , λ _ → ∣ -↠-refl ∣)
      □*→Λ-is-constant M₀ y@(M , x , r) = begin
        □map (*→Λ M₀) .fst y
          ≡⟨ refl ⟩
        ↑₁ M₀ [ M ] , next M₀ , (λ α → ∥-∥map F⊩f (r α))
          ≡⟨ cong₂ {C = λ _ _ → ⟨ □ k Λ₀ₐ ⟩} (λ L N → (L , next M₀ , N)) (subst-rename-∅ _ M₀) {!!} ⟩
        M₀ , next M₀ , (λ α → ∣ -↠-refl ∣) ∎
        where
          open ≡-Reasoning
          open HasTracker (*→Λ M₀ .snd)


      natural-on-*→Λ : (M : Λ₀) → qQ-at-Λ ∘ *→Λ M ∼ □map (*→Λ M) ∘ qQ-at-⊤ ꞉ ⊤ₐ →ₐ □ k Λ₀ₐ
      natural-on-*→Λ M = naturality (*→Λ M)

      lem : (M : Λ₀) → qΛ M ≡ (M , next M , λ _ → ∣ -↠-refl ∣)
      lem M = begin
        qΛ M
          ≡⟨ refl ⟩
        qΛ (*→Λ M .fst _)
          ≡⟨ natural-on-*→Λ M _ ⟩
        □map (*→Λ M) .fst (qQ-at-⊤ .fst _)
          ≡⟨ □*→Λ-is-constant M (qQ-at-⊤ .fst _) ⟩
        (M , next M , λ _ → ∣ -↠-refl ∣) ∎
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

  GL : {X : Asm 𝓤}
    → Trackable (□ k X) X
    → Trackable ⊤ₐ X
  GL {k = k} {X} (f , F , F⊩f) = Final.global-element x (F [ ⌜ gfix′ F ⌝ ]) r
    where
      module X  = AsmStr (str X)

      f′ : (▹ k (Σ[ x ꞉ ⟨ X ⟩ ] F [ ⌜ gfix (ƛ F) ⌝ ] X.⊩ x))
        → Σ[ x ꞉ ⟨ X ⟩ ] F [ ⌜ gfix′ F ⌝ ] X.⊩ x
      f′ hyp = f (gfix′ F , (λ α → hyp α .fst) , λ α → ∣ X.⊩-respects-↠ gfix′-↠ (hyp α .snd) ∣) ,
        F⊩f (lift -↠-refl)

      fixf : Σ[ x ꞉ ⟨ X ⟩ ] F [ ⌜ gfix′ F ⌝ ] X.⊩ x
      fixf = fix f′

      x = fixf .fst
      r = fixf .snd


  IGL : (X : Asm 𝓤)
    → Trackable (□ k (□ k X ⇒ X)) (□ k X)
  IGL {k = k} X = irec , ↑₁ Sub · {!!} · (↑₁ ⌜ gfix {!0!} ⌝) , λ {G} {g} r → lift {!!}
    where
      module X  = AsmStr (str X)
      module □X = AsmStr (str (□ k X))

      irec : ⟨ □ k (□ k X ⇒ X) ⟩ → ⟨ □ k X ⟩
      irec (F , f , F⊩f) = F · ⌜ gfix F ⌝  , ▹Σ y
        where
          y : ▹ k (Σ[ x ꞉ ⟨ X ⟩ ] ∥ F · ⌜ gfix F ⌝ X.⊩ x ∥) 
          y α = fix λ hyp →
            f α .fst (gfix F , (λ α → hyp α .fst) ,
              λ α → rec propTruncIsProp (λ r → ∣ X.⊩-respects-↠ gfix-↠ r ∣) (hyp α .snd)) ,
            rec propTruncIsProp (λ r → ∣ r (lift -↠-refl) ∣) (F⊩f α)
