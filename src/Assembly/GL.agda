{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.GL where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub; r)
open import Later

open import Calculus.Untyped
  hiding (Z)
  
open import Assembly.Base
open import Assembly.Properties
open import Assembly.ClockedExposure

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
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ ▹x ꞉ ▹ k ⟨ X ⟩ ] ▹[ α ꞉ k ] M X.⊩ ▹x α

      _⊩_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩ (M , _ , _)= Lift (n̅ -↠ ⌜ M ⌝)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , ▹x , M⫣x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map₀ : Trackable X Y → ⟨ □ k X ⟩ → ⟨ □ k Y ⟩
  □map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ] , ▹map f x , λ α → F⊩f (M⊩x α) -- λ α → ∥-∥map F⊩f (M⊩x α)

  □map₁ : Λ₁ → Λ₁
  □map₁ F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

  □map : (k : Cl) → Trackable X Y → Trackable (□ k X) (□ k Y)
  □map {𝓤} {X} {Y} _ Ff@(f , F , f⫣F) = □map₀ Ff , □map₁ F , 
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
  □id=id X (M , x , M⊩x) i = M , x , M⊩x -- propTruncIsProp (∥-∥map (λ x → x) (M⊩x α)) (M⊩x α) i

  □gf=□g□f : (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ □ k X ⟩) → □map₀ (g ∘ f) x ≡ □map₀ g (□map₀ f x)
  □gf=□g□f {Z = Z} (f , F , F⊩f) (g , G , G⊩g) (M , x , r) i = G[F[M]]=G[F][M] i , ▹map g (▹map f x) , λ α →
    transport-filler (cong (Z._⊩ (▹map g (▹map f x) α)) (G[F[M]]=G[F][M] ⁻¹)) (G⊩g (F⊩f (r α))) (~ i)
    where
      module Z = AsmStr (str Z)
      G[F[M]]=G[F][M] = ∘-ssubst-ssubst G F M

  □reflects∼ : (f g : Trackable X Y)
    → isSet ⟨ Y ⟩
    → ((k : Cl) → □map k f ∼ □map k g ꞉ □ k X →ₐ □ k Y)
    → f ∼ g ꞉ X →ₐ Y
  □reflects∼ {X = X} (f , F , F⊩f) (g , G , G⊩g) YisSet □f∼□g x = rec (YisSet _ _)
    (λ { (M , r) → {!!} }) 
    (X.⊩-right-total x)
    where
      module X = AsmStr (str X)

  □-isExposure : IsCloExpo {𝓤} □ □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = {!!}
    }

  □F=□G→F=G : (F G : Λ₁) → □map₁ F ≡ □map₁ G → F ≡ G
  □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decode (encode □F=□G .fst .snd)))
    where
      postulate
        ↑ₗ-injective : {Γ Δ : Cxt} {A : 𝕋} {M N : Δ ⊢ A} → ↑ₗ_ {Δ} {_} {Γ} M ≡ ↑ₗ N → M ≡ N

  □-exposure : CloExpo 𝓤
  □-exposure = exposure □ □map □-isExposure

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ k (⊥ₐ {𝓤}) ⟩ → ⊥* {𝓤}) → ▹ k ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ k ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- Theorem: There is no natural transformation q : I ⇒ □.
  -- Proof sketch: By naturality, qΛ is determined by its component at the terminal object ⊤ₐ. 
  
  quoting-does-not-exist : Cl → (q : NaturalTransformation {𝓤₀} Id □-exposure) → ⊥
  quoting-does-not-exist k′ (fun , naturality) = quoting-not-definable (QΛ k′ , QΛ-is-quoting k′)
    where
      qQ-at-Λ : (k : Cl) → Trackable Λ₀ₐ (□ k Λ₀ₐ)
      qQ-at-Λ k = fun k

      qΛ = λ (k : Cl) → qQ-at-Λ k .fst
      QΛ = λ (k : Cl) → HasTracker.F (qQ-at-Λ k .snd)

      qQ-at-⊤ : (k : Cl) → Trackable ⊤ₐ (□ k ⊤ₐ)
      qQ-at-⊤ k = fun k
     
      QΛ[M] : {N M : Λ₀} → N -↠ M → Lift (QΛ k [ N ] -↠ ⌜ qΛ k M .fst ⌝)
      QΛ[M] = HasTracker.F⊩f (qQ-at-Λ _ .snd) 

      lem : (k : Cl) → (M : Λ₀) → qΛ k M ≡ (M , next M , _)
      lem k M = begin
        qΛ k M
          ≡⟨ refl ⟩
        qΛ k (*→Λ M .fst _)
          ≡⟨ naturality k (*→Λ M) _ ⟩
        □map k (*→Λ M) .fst (qQ-at-⊤ k .fst tt*)
          ≡⟨ refl ⟩
        ↑₁ M [ _ ]  , next M , (λ α → s α)
          ≡[ i ]⟨ subst-rename-∅ _ M i , next M , transport-filler (cong (λ N → ▹ k (N -↠ M)) (subst-rename-∅ _ M)) s i ⟩
        M , next M , subst (λ N → ▹ k (N -↠ M)) (subst-rename-∅ _ M) s ∎
        where
          open ≡-Reasoning
          open HasTracker (*→Λ M .snd)
          f : Unit* → ⟨ □ k ⊤ₐ ⟩
          f = qQ-at-⊤ k .fst
          s = ▹map F⊩f (f tt* .snd .snd)
  
      QΛ-is-quoting : (k : Cl)
        → (M : Λ₀) → QΛ k [ M ] -↠ ⌜ M ⌝
      QΛ-is-quoting k M = begin
        QΛ k [ M ]
          -↠⟨ lower (QΛ[M] -↠-refl) ⟩
        ⌜ qΛ k M .fst ⌝
        ≡[ i ]⟨ ⌜ lem k M i .fst  ⌝ ⟩
        ⌜ M ⌝ ∎
        where open -↠-Reasoning

  GL : {X : Asm 𝓤}
    → Trackable (□ k X) X
    → Trackable ⊤ₐ X
  GL {k = k} {X} (f , F , F⊩f) = Final.global-element (fixf .fst) (F [ ⌜ gfix′ F ⌝ ]) (fixf .snd)
    where
      module X  = AsmStr (str X)

      f′ : Σ[ x ꞉ ▹ k ⟨ X ⟩ ] ▹[ α ꞉ k ] F [ ⌜ gfix (ƛ F) ⌝ ] X.⊩ x α
        → Σ[ x ꞉ ⟨ X ⟩ ] F [ ⌜ gfix′ F ⌝ ] X.⊩ x
      f′ (x , r) = f (gfix′ F , x , λ α → X.⊩-respects-↠ gfix′-↠ (r α)) , F⊩f (lift -↠-refl)

      fixf : Σ[ x ꞉ ⟨ X ⟩ ] F [ ⌜ gfix′ F ⌝ ] X.⊩ x
      fixf = fixΣ f′

  -- IGL : (X : Asm 𝓤)
  --   → Trackable (□ k (□ k X ⇒ X)) (□ k X)
  -- IGL {k = k} X = irec , ↑₁ Sub · {!!} · (↑₁ ⌜ gfix {!0!} ⌝) , λ {G} {g} r → lift {!!}
  --   where
  --     module X  = AsmStr (str X)
  --     module □X = AsmStr (str (□ k X))

  --     irec : ⟨ □ k (□ k X ⇒ X) ⟩ → ⟨ □ k X ⟩
  --     irec (F , f , F⊩f) = F · ⌜ gfix F ⌝  , ▹Σ y
  --       where
  --         y : ▹ k (Σ[ x ꞉ ⟨ X ⟩ ] ∥ F · ⌜ gfix F ⌝ X.⊩ x ∥) 
  --         y α = fix λ hyp →
  --           f α .fst (gfix F , (λ α → hyp α .fst) ,
  --             λ α → rec propTruncIsProp (λ r → ∣ X.⊩-respects-↠ gfix-↠ r ∣) (hyp α .snd)) ,
  --           rec propTruncIsProp (λ r → ∣ r (lift -↠-refl) ∣) (F⊩f α)
