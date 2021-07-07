{-# OPTIONS --guarded #-}

module Assembly.GL where

open import Prelude 
  hiding (id; _∘_; r)
open import Later

open import Calculus.Untyped
  
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
  □ {𝓤} k ((|X| , XisSet) , Xstr) = (|□X| , isSet□X) , _⊩_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩-right-total
    ; ⊩-isSet       = isOfHLevelLift 2 -↠isSet 
    }
    where
      module X = AsmStr Xstr
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ∶ Λ₀ ] Σ[ ▹x ∶ ▹ k |X| ] ▹[ α ∶ k ] M X.⊩ ▹x α
      
      isSet□X : isSet |□X|
      isSet□X = isSetΣ ≟→isSet λ _ → isSetΣ (▹isSet→isSet▹ (λ _ → XisSet)) (λ _ → ▹isSet→isSet▹ (λ α → X.⊩-isSet))

      _⊩_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩ (M , _)= Lift (n̅ -↠ ⌜ M ⌝)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N N-↠⌜L⌝ = lift (-↠-trans M-↠N (lower N-↠⌜L⌝))
      
      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , _) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map₀ : Trackable X Y → ⟨ □ k X ⟩ → ⟨ □ k Y ⟩
  □map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ] , ▹map f x , λ α → F⊩f (M⊩x α) 

  □map₁ : Λ₁ → Λ₁
  □map₁ F = ↑ Sub · ↑ ⌜ F ⌝ · 0

  □map : (k : Cl) → Trackable X Y → Trackable (□ k X) (□ k Y)
  □map {𝓤} {X} {Y} _ Ff@(f , F , _) = □map₀ Ff , □map₁ F , 
    λ {M} {x} → □F⊩□f {_} {M} {x}
    where
      open -↠-Reasoning
      □F⊩□f : Tracks (□ k X) (□ k Y) (□map₁ F) (□map₀ Ff)
      □F⊩□f {_} {n̅} {M , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑ Sub [ n̅ ] · ↑ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = fsuc} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = fsuc} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  □id=id : (X : Asm 𝓤) → (x : ⟨ □ k X ⟩) → □map₀ (id X) x ≡ x
  □id=id X Mxr = refl

  □gf=□g□f : {X Y Z : Asm 𝓤} (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ □ k X ⟩) → □map₀ (g ∘ f) x ≡ □map₀ g (□map₀ f x)
  □gf=□g□f {Z = Z} (f , F , F⊩f) (g , G , G⊩g) (M , x , r) i = G[F[M]]=G[F][M] i , ▹map g (▹map f x) , λ α →
    transport-filler (cong (Z._⊩ (▹map g (▹map f x) α)) (G[F[M]]=G[F][M] ⁻¹)) (G⊩g (F⊩f (r α))) (~ i)
    where
      module Z = AsmStr (str Z)
      G[F[M]]=G[F][M] = ∘-ssubst-ssubst G F M

  □reflects∼ : {X Y : Asm 𝓤} (f g : Trackable X Y)
    → ((k : Cl) → □map k f ∼ □map k g)
    → (k : Cl) → f ∼ g
  □reflects∼ {𝓤} {X} {Y} (f , F , F⊩f) (g , G , G⊩g) □f∼□g k x = rec ((Y is-set) _ _)
    (λ { (M , r) → ▹x=▹y→x=y  (λ k → cong (λ x → fst (snd x)) (□f∼□g k (M , next x , next r))) k })
    (X.⊩-right-total x) 
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

  □-isExposure : IsCloExpo {𝓤} □ □map
  □-isExposure = record
    { preserve-id   = □id=id
    ; preserve-comp = □gf=□g□f
    ; reflects-∼    = □reflects∼
    }

  □F=□G→F=G : (F G : Λ₁) → □map₁ F ≡ □map₁ G → F ≡ G
  □F=□G→F=G F G □F=□G = ⌜⌝-injective (↑ₗ-injective (decode (encode □F=□G .fst .snd)))
    where
      postulate
        ↑ₗ-injective : {n m : ℕ} {M N : Λ m} → ↑_ {m} {n} M ≡ ↑ N → M ≡ N

  □-exposure : CloExpo 𝓤
  □-exposure = exposure □ □map □-isExposure

  □⊤ : Trackable (⊤ₐ {𝓤}) (□ k ⊤ₐ)
  □⊤ = Final.global-element ⌜ 𝑰 ⌝ (𝑰 , next tt* , next (lift -↠-refl)) (lift -↠-refl)
    where open -↠-Reasoning
    
  |K| : ⟨ □ k (X ⇒ Y) ⟩ → ⟨ □ k X ⇒ □ k Y ⟩
  |K| (ƛF , f , 𝔣) =
    ( λ{ (M , x , r) → ƛF · M , (λ α → f α .fst (x α)) , λ α → 𝔣 α (r α)})
    , ∣ App ⟪ exts (subst-zero ⌜ ƛF ⌝) ⟫ , (λ { {N} {M , _ , _} s → lift (begin
      App ⟪ exts (subst-zero ⌜ ƛF ⌝) ⟫ [ N ]
        -↠⟨ reduce-ssubst (App ⟪ exts (subst-zero ⌜ ƛF ⌝) ⟫) (lower s) ⟩
      App ⟪ exts (subst-zero ⌜ ƛF ⌝) ⟫ [ ⌜ M ⌝ ]
        -↠⟨ App-↠ ⟩
      ⌜ (ƛF) · M ⌝ ∎)} ) ∣
    where
      open -↠-Reasoning

  K : (X Y : Asm 𝓤) → Trackable (□ k (X ⇒ Y)) (□ k X ⇒ □ k Y)
  K X Y = |K| , ƛ App , λ { {H} {G , _} (lift H↠⌜G⌝) {N} {M , _} (lift t)→ lift (begin
    (ƛ App ⟪ exts (subst-zero H) ⟫) · N
      -↠⟨ ·ᵣ-cong t ⟩
    (ƛ App ⟪ exts (subst-zero H) ⟫) · ⌜ M ⌝
      -↠⟨ ·ₗ-cong (ƛ-cong (reduce-subst App (extsσ-↠σ′ λ { fzero → H↠⌜G⌝ }))) ⟩
    (ƛ App ⟪ exts (subst-zero ⌜ G ⌝) ⟫) · ⌜ M ⌝
      -→⟨ β ⟩
    App ⟪ exts (subst-zero ⌜ G ⌝) ⟫ [ ⌜ M ⌝ ]
      -↠⟨ App-↠ ⟩
    ⌜ G · M ⌝ ∎ )} 
    where
      open -↠-Reasoning

  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ k (⊥ₐ {𝓤}) ⟩ → ⊥* {𝓤}) → ▹ k ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ k ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist e = fix (bang (e .fst))

  -- Theorem: There is no natural transformation q : I ⇒ □.
  -- Proof sketch: By naturality, qΛ is determined by its component at the terminal object ⊤ₐ. 
  
  quoting-does-not-exist : Cl → (q : NaturalTransformation {𝓤₀} Id □-exposure) → ⊥
  quoting-does-not-exist k′ (fun , naturality) = quoting′-not-definable (QΛ k′ , QΛ-is-quoting k′)
    where
      -- qQ-at-Λ : (k : Cl) → Trackable Λ₀ₐ (□ k Λ₀ₐ)
      qQ-at-Λ = λ (k : Cl) → fun k Λ₀ₐ
      qQ-at-⊤ = λ (k : Cl) → fun k ⊤ₐ

      qΛ = λ (k : Cl) → qQ-at-Λ k .fst
      QΛ = λ (k : Cl) → HasTracker.F (qQ-at-Λ k .snd)
     
      QΛ[M] : {N M : Λ₀} → N -↠ M → Lift (QΛ k [ N ] -↠ ⌜ qΛ k M .fst ⌝)
      QΛ[M] = HasTracker.F⊩f (qQ-at-Λ _ .snd) 

      lem : (k : Cl) → (M : Λ₀) → qΛ k M ≡ (M , next M , _)
      lem k M = begin
        qΛ k M
          ≡⟨ refl ⟩
        qΛ k (*→Λ M .fst _)
          ≡⟨ naturality (*→Λ M) _ ⟩
        □map k (*→Λ M) .fst (qQ-at-⊤ k .fst tt*)
          ≡⟨ refl ⟩
        ↑ M [ _ ]  , next M , (λ α → s α)
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

  _† : Trackable (□ k X) X
     → Trackable ⊤ₐ (□ k X)
  _† {k} {_} {X} (|f| , F , 𝔣) = Final.global-element ⌜ sfix F ⌝ (sfix F , fixf) (lift -↠-refl)
    where
      module X = AsmStr (str X)
      fold : (x : ▹ k ⟨ X ⟩) → ▹[ α ∶ k ] F [ ⌜ sfix F ⌝ ] X.⊩ x α
           → ▹[ α ∶ k ] sfix F X.⊩ x α
      fold x r α = X.⊩-respects-↠ sfix-↠ (r α)

      h : Σ[ x ∶ ▹ k ⟨ X ⟩ ] ▹[ α ∶ k ] F [ ⌜ sfix F ⌝ ] X.⊩ x α
        → Σ[ x ∶     ⟨ X ⟩ ]            F [ ⌜ sfix F ⌝ ] X.⊩ x
      h (x , r) = |f| (sfix F , x , fold x r) , 𝔣 (lift -↠-refl)

      fixf : Σ[ x ∶ ▹ k ⟨ X ⟩ ] ▹[ α ∶ k ] sfix F X.⊩ x α
      fixf = dfixΣ h .fst , fold (dfixΣ h .fst) (dfixΣ h .snd)

  run : (∀ k → ⟨ □ k X ⟩) → (k′ : Cl) → ⟨ X ⟩
  run {X = X} x k′ = force x′ k′
    where
      x′ : ∀ k → ▹ k ⟨ X ⟩
      x′ k α = x k .snd .fst α
      
  _‡ : Trackable (□ k X) X
     → Trackable ⊤ₐ X
  _‡ {k} {_} {X} (|f| , F , 𝔣) =
    Final.global-element (sfix F) fixf fixr
    where
      module X = AsmStr (str X)
      fold : (x : ▹ k ⟨ X ⟩) → ▹[ α ∶ k ] F [ ⌜ sfix F ⌝ ] X.⊩ x α
           → ▹[ α ∶ k ] sfix F X.⊩ x α
      fold x r α = X.⊩-respects-↠ sfix-↠ (r α)

      h : Σ[ x ∶ ▹ k ⟨ X ⟩ ] ▹[ α ∶ k ] F [ ⌜ sfix F ⌝ ] X.⊩ x α
        → Σ[ x ∶     ⟨ X ⟩ ]            F [ ⌜ sfix F ⌝ ] X.⊩ x
      h (x , r) = |f| (sfix F , x , fold x r) , 𝔣 (lift -↠-refl)

      fixf : ⟨ X ⟩
      fixf = fixΣ h .fst

      fixr : sfix F X.⊩ fixf
      fixr = X.⊩-respects-↠ sfix-↠ (fixΣ h .snd)

{-
  □′ has a different but equivalent defininition from □.

  The later modality now lives outside the second Σ-type:

      |□X| = Σ[ M ∶ Λ₀ ] ▹ k (Σ[ x ∶ ⟨ X ⟩ ] M X.⊩ x)

  instead of inside the second Σ-type:

      |□X| = Σ[ M ∶ Λ₀ ] Σ[ ▹x ∶ ▹ k |X| ] ▹[ α ∶ k ] M X.⊩ ▹x α
-}
  □′ : (k : Cl) → Asm 𝓤 → Asm 𝓤
  □′ {𝓤} k X = (|□X| , isSet□X) , _⊩_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩-right-total
    ; ⊩-isSet       = isOfHLevelLift 2 -↠isSet 
    }
    where
      module X = AsmStr (str X)
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ∶ Λ₀ ] ▹ k (Σ[ x ∶ ⟨ X ⟩ ] M X.⊩ x)
      
      isSet□X : isSet |□X|
      isSet□X = isSetΣ ≟→isSet λ _ → ▹isSet→isSet▹ λ _ → isSetΣ (X is-set) (λ _ → X.⊩-isSet)

      _⊩_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩ (M , _)= Lift (n̅ -↠ ⌜ M ⌝)

      ⊩-respect-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩-right-total :  _⊩_ IsRightTotal
      ⊩-right-total (M , _) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □′map₀ : Trackable X Y
    → ⟨ □′ k X ⟩ → ⟨ □′ k Y ⟩
  □′map₀ (|f| , F , F⊩f) (M , x) = F [ M ] , λ α → |f| (x α .fst) , F⊩f (x α .snd)
      
  module _ {X : Asm 𝓤} where
    module X = AsmStr (str X)
  
    _†′ : Trackable (□′ k X) X
      →  Trackable ⊤ₐ       (□′ k X)
    _†′ {k} (|f| , F , F⊩f) = Final.global-element ⌜ sfix F ⌝ (sfix F , fixf′) (lift -↠-refl)
      where
        backward : Σ[ x ∶ ⟨ X ⟩ ] F [ ⌜ sfix F ⌝ ] X.⊩ x → Σ[ x ∶ ⟨ X ⟩ ] sfix F X.⊩ x
        backward (x , r) = x , X.⊩-respects-↠ sfix-↠ r

        h : ▹ k (Σ[ x ∶ ⟨ X ⟩ ] F [ ⌜ sfix F ⌝ ] X.⊩ x)
          →     Σ[ x ∶ ⟨ X ⟩ ] F [ ⌜ sfix F ⌝ ] X.⊩ x
        h x = |f| (sfix F , ▹map backward x) , F⊩f (lift -↠-refl)

        fixf′ : ▹ k (Σ[ x ∶ ⟨ X ⟩ ] sfix F X.⊩ x)
        fixf′ α = backward (dfix h α)

        fixf′-path : Path ⟨ □′ k X ⟩ (sfix F , fixf′) (sfix F , λ _ → |f| (sfix F , fixf′) , X.⊩-respects-↠ sfix-↠ (F⊩f (lift -↠-refl)))
        fixf′-path = begin
          sfix F , fixf′
            ≡⟨ refl ⟩
          sfix F , (λ α → backward (dfix h α))
            ≡⟨ cong {B = λ _ → ⟨ □′ k X ⟩} (sfix F ,_) (λ i α → backward (pfix h i α)) ⟩
          sfix F , (λ α → backward (h (dfix h)))
            ≡⟨ refl ⟩
          sfix F , (λ α → backward (|f| (sfix F , ▹map backward (dfix h)) , F⊩f (lift -↠-refl)))
            ≡⟨ refl ⟩
          sfix F , (λ α → |f| (sfix F , ▹map backward (dfix h)) , X.⊩-respects-↠ sfix-↠ (F⊩f (lift -↠-refl)))
            ≡⟨ refl ⟩
          sfix F , (λ α → |f| (sfix F , fixf′) , X.⊩-respects-↠ sfix-↠ (F⊩f (lift -↠-refl))) ∎
          where open ≡-Reasoning

    _‡′ : Trackable (□′ k X) X
      → Trackable ⊤ₐ X 
    _‡′ {k} (|f| , F , 𝔣) =
      Final.global-element (sfix F) (fixf .fst) (fixf .snd)
      where
        backward : Σ[ x ∶ ⟨ X ⟩ ] F [ ⌜ sfix F ⌝ ] X.⊩ x → Σ[ x ∶ ⟨ X ⟩ ] sfix F X.⊩ x
        backward (x , r) = x , X.⊩-respects-↠ sfix-↠ r

        h : ▹ k (Σ[ x ∶ ⟨ X ⟩ ] F [ ⌜ sfix F ⌝ ] X.⊩ x)
          →     Σ[ x ∶ ⟨ X ⟩ ] F [ ⌜ sfix F ⌝ ] X.⊩ x
        h x = |f| (sfix F , ▹map backward x) , 𝔣 (lift -↠-refl)

        fixf : Σ[ x ∶ ⟨ X ⟩ ] sfix F X.⊩ x
        fixf = backward (fix h)

        -- fixpoint equation
        fixf-path : fixf .fst ≡ |f| (sfix F , next fixf)
        fixf-path = begin
          backward (fix h) .fst
            ≡⟨ cong (λ x → backward x .fst) (fix-path h) ⟩
          backward (h (next (fix h))) .fst 
            ≡⟨ refl ⟩
          backward (|f| (sfix F , ▹map backward (next (fix h))) , 𝔣 (lift -↠-refl)) .fst
            ≡⟨ refl ⟩
          |f| (sfix F , ▹map backward (next (fix h)))
            ∎
          where open ≡-Reasoning

    |IGL| : ⟨ □′ k (□′ k X ⇒ X) ⟩ → ⟨ □′ k X ⟩
    |IGL| {k} f@(ƛF , |f|) = gfix ƛF , λ α → backward (fix h α)
      where
        backward : Σ[ x ∶ ⟨ X ⟩ ] ƛF · ⌜ gfix ƛF ⌝ X.⊩ x → Σ[ x ∶ ⟨ X ⟩ ] gfix ƛF X.⊩ x
        backward (x , r) = x , X.⊩-respects-↠ gfix-↠ r

        h : ▹ k (▹ k (Σ[ x ∶ ⟨ X ⟩ ] ƛF · ⌜ gfix ƛF ⌝ X.⊩ x))
          → ▹ k (Σ[ x ∶ ⟨ X ⟩ ] ƛF · ⌜ gfix ƛF ⌝ X.⊩ x)
        h x α = |f| α .fst .fst (gfix ƛF , ▹map backward (x α))
          , |f| α .snd (lift -↠-refl) 

    IGL : Trackable (□′ k (□′ k X ⇒ X)) (□′ k X)
    IGL = |IGL| , igfix , λ { {G} {ƛF , ▹f} (lift r) → lift (begin
      igfix [ G ]
        -↠⟨ reduce-ssubst igfix r ⟩
      igfix [ ⌜ ƛF ⌝ ]
        -↠⟨ igfix-↠ ⟩
      ⌜ gfix ƛF ⌝ ∎)}
       where open -↠-Reasoning
