{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.S4 where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub)

open import Calculus.Untyped
  
open import Assembly.Base
open import Assembly.Properties
open import Assembly.Exposure

private
  variable
    X Y Z : Asm 𝓤

module _ (Q : Quoting) where
  open Quoting Q

  ⊠_ : Asm 𝓤 → Asm 𝓤
  ⊠_ {𝓤} X@((|X| , XisSet) , _⊩_ , _) = (|⊠X| , isSet⊠X) , _⊩⊠X_ , record
    { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩⊠X-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩⊠X-right-total
    ; ⊩-isSet       = isOfHLevelLift 2 -↠isSet
    }
    where
      module X = AsmStr (str X)
      |⊠X| : 𝓤 ̇
      |⊠X| = Σ[ M ∶ Λ₀ ] Σ[ x ∶ |X| ] M ⊩ x

      isSet⊠X : isSet |⊠X|
      isSet⊠X = isSetΣ (Discrete→isSet _≟_) λ M → isSetΣ XisSet λ _ → X.⊩-isSet
      -- Can we remove truncation? Yes.

      _⊩⊠X_ : (M : Λ₀) → |⊠X| → 𝓤 ̇
      n̅ ⊩⊠X (M , _ , _) = Lift (n̅ -↠ ⌜ M ⌝)

      ⊩⊠X-respect-↠ : _⊩⊠X_ respects _-↠_ on-the-left
      ⊩⊠X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
   
      ⊩⊠X-right-total :  _⊩⊠X_ IsRightTotal
      ⊩⊠X-right-total (M , _ , M⫣x) = ∣ ⌜ M ⌝ , lift (⌜ M ⌝ _-↠_.∎) ∣

  ⊠map₀ : {X Y : Asm 𝓤} → Trackable X Y → ⟨ ⊠ X ⟩ → ⟨ ⊠ Y ⟩
  ⊠map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ] , f x , F⊩f M⊩x

  ⊠map₁ : Λ₁ → Λ₁
  ⊠map₁ F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

  ⊠map : {X Y : Asm 𝓤} → Trackable X Y → Trackable (⊠ X) (⊠ Y)
  ⊠map {𝓤} {X} {Y} Ff@(f , F , f⫣F) = ⊠map₀ Ff , ⊠map₁ F , 
    λ {M} {x} → ⊠F⊩⊠f {M} {x}
    where
      open -↠-Reasoning
      ⊠F⊩⊠f : Tracks (⊠ X) (⊠ Y) (⊠map₁ F) (⊠map₀ Ff)
      ⊠F⊩⊠f {n̅} {M , _ , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = fsuc} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = fsuc} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  ⊠id=id : (X : Asm 𝓤) → (x : ⟨ ⊠ X ⟩) → ⊠map₀ (id X) x ≡ x
  ⊠id=id X x = refl

  ⊠gf=⊠g⊠f : {X Y Z : Asm 𝓤} (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ ⊠ X ⟩) → ⊠map₀ (g ∘ f) x ≡ ⊠map₀ g (⊠map₀ f x)
  ⊠gf=⊠g⊠f {𝓤} {Z = Z} (f , F , F⊩f) (g , G , G⊩g) (M , x , r) i =
    G[F[M]]=G[F][M] i , g (f x) , transport-filler (cong (Z._⊩ g (f x)) (G[F[M]]=G[F][M] ⁻¹)) (G⊩g (F⊩f r)) (~ i)
    where
      module Z = AsmStr (str Z)
      G[F[M]]=G[F][M] = ∘-ssubst-ssubst G F M
      
  ⊠reflects∼ : {X Y : Asm 𝓤} (f g : Trackable X Y)
    → ⊠map f ∼ ⊠map g
    → f ∼ g
  ⊠reflects∼ {𝓤} {X} {Y} f g ⊠f=⊠g x = rec ((Y is-set) _ _)
    (λ { (M , M⊩x) → cong (λ x → fst (snd x)) (⊠f=⊠g (M , x , M⊩x))  })
    (X.⊩-right-total x)
    where
      module X = AsmStr (str X)

  ⊠-isExposure : IsExposure {𝓤} ⊠_  ⊠map
  ⊠-isExposure = record
    { preserve-id   = ⊠id=id
    ; preserve-comp = ⊠gf=⊠g⊠f
    ; reflects-∼    = ⊠reflects∼
    }

  ⊠-exposure : Exposure 𝓤
  ⊠-exposure = exposure ⊠_ ⊠map ⊠-isExposure
  
  ⊠F=⊠G→F=G : (F G : Λ₁) → ⊠map₁ F ≡ ⊠map₁ G → F ≡ G
  ⊠F=⊠G→F=G F G ⊠F=⊠G = ⌜⌝-injective (↑ₗ-injective (decode (encode ⊠F=⊠G .fst .snd)))
    where
      postulate ↑ₗ-injective : ∀ {m n} {M N : Λ n} → ↑ₗ_ {n} {m} M ≡ ↑ₗ N → M ≡ N

  ⊤→⊠⊤ : Trackable (⊤ₐ {𝓤}) (⊠ ⊤ₐ)
  ⊤→⊠⊤ = (λ _ → (𝑰 , tt* , lift -↠-refl)) , (↑₁ ⌜ 𝑰 ⌝) , λ { (lift M-↠𝑰) → lift (begin
    (↑₁ ⌜ 𝑰 ⌝) [ _ ]
      ≡⟨ subst-rename-∅ _ _ ⟩
    ⌜ 𝑰 ⌝ ∎) }
    where
      open -↠-Reasoning

  ⊠X×Y→⊠X : {X Y : Asm 𝓤} → Trackable (⊠ (X ×ₐ Y)) (⊠ X)
  ⊠X×Y→⊠X {𝓤} {X} {Y} = (λ { (L , (x , _) , ((M , red , r) , _)) → ( (ƛ 0 · ↑₁ 𝑻) · L , x , X.⊩-respects-↠ (begin
    (ƛ 0 · ↑₁ 𝑻) · L
      -→⟨ β ⟩
    L · ↑₁ 𝑻 [ L ]
      -↠⟨ red ⟩
    M ∎) r) }) ,
    ↑₁ Ap · ↑₁ ⌜ ƛ 0 · ↑₁ 𝑻 ⌝ · 0   , (λ { {M}  {L , _} r → lift (begin
    ↑₁ Ap [ M ] · ↑₁ ⌜ ƛ 0 · ↑₁ 𝑻  ⌝ [ M ] · M
      ≡⟨ cong₂ (λ L N → L · N · M) (subst-rename-∅ _ Ap) (subst-rename-∅ _ ⌜ ƛ 0 · ↑₁ 𝑻 ⌝) ⟩
    Ap · ⌜ ƛ 0 · ↑₁ 𝑻 ⌝ · M
      -↠⟨ ·ᵣ-cong (lower r) ⟩
    Ap · ⌜ ƛ 0 · ↑₁ 𝑻 ⌝ · ⌜ _ ⌝
      -↠⟨ Ap-↠ ⟩
    ⌜ (ƛ 0 · ↑₁ 𝑻) · L ⌝ ∎ )})
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

  ⊠X×Y→⊠Y : {X Y : Asm 𝓤} → Trackable (⊠ (X ×ₐ Y)) (⊠ Y)
  ⊠X×Y→⊠Y {𝓤} {X} {Y} = (λ { (L , (_ , y) , (_ , (N , red , s))) → ( (ƛ 0 · ↑₁ 𝑭) · L , y , Y.⊩-respects-↠ (begin
    (ƛ 0 · ↑₁ 𝑭) · L -→⟨ β ⟩ L · ↑₁ 𝑭 [ L ] -↠⟨ red ⟩ N ∎) s) }) ,
    ↑₁ Ap · ↑₁ ⌜ ƛ 0 · ↑₁ 𝑭 ⌝ · 0   , (λ { {M}  {L , _} r → lift (begin
    ↑₁ Ap [ M ] · ↑₁ ⌜ ƛ 0 · ↑₁ 𝑭  ⌝ [ M ] · M
      ≡⟨ cong₂ (λ L N → L · N · M) (subst-rename-∅ _ Ap) (subst-rename-∅ _ ⌜ ƛ 0 · ↑₁ 𝑭 ⌝) ⟩
    Ap · ⌜ ƛ 0 · ↑₁ 𝑭 ⌝ · M
      -↠⟨ ·ᵣ-cong (lower r) ⟩
    Ap · ⌜ ƛ 0 · ↑₁ 𝑭 ⌝ · ⌜ _ ⌝
      -↠⟨ Ap-↠ ⟩
    ⌜ (ƛ 0 · ↑₁ 𝑭) · L ⌝ ∎ )})
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

  eval : {X : Asm 𝓤} → Trackable (⊠ X) X
  eval {X = X} = (λ x → fst (snd x)) , Eval ,
    λ { {N} {M , x , M⊩x} N-↠⌜M⌝ →
      X.⊩-respects-↠ (reduce-ssubst Eval (lower N-↠⌜M⌝)) ((X.⊩-respects-↠ Eval-↠ M⊩x)) }
    where
      module X  = AsmStr (str X)
      module ⊠X = AsmStr (str (⊠ X))

  eval-nat : {𝓤 : Universe} → NaturalTransformation {𝓤} ⊠-exposure Id
  eval-nat = eval , λ f x → refl

  quoting : {X : Asm 𝓤} → Trackable (⊠ X) (⊠ ⊠ X)
  quoting {X = X} = (λ { y@(M , x , r) → ⌜ M ⌝ , y , lift -↠-refl }) , Quote , λ where
    {N} {M , x , r} (lift N-↠⌜M⌝) → lift (begin
      Quote [ N ]
        -↠⟨ reduce-ssubst Quote N-↠⌜M⌝ ⟩
      Quote [ ⌜ M ⌝ ]
        -↠⟨ Quote-↠ ⟩
      ⌜ ⌜ M ⌝ ⌝ ∎)
      where
        open -↠-Reasoning
        module ⊠X  = AsmStr (str (⊠ X))
        module ⊠⊠X = AsmStr (str (⊠ ⊠ X))

  quoting′-does-not-exist : (q : NaturalTransformation {𝓤₀} Id ⊠-exposure) → ⊥
  quoting′-does-not-exist (fun , naturality) = quoting′-not-definable (QΛ , QΛ-is-quoting)
    where
      q-at-Λ : Trackable Λ₀ₐ (⊠ Λ₀ₐ)
      q-at-Λ = fun

      qΛ : Λ₀ → Σ[ N ∶ Λ₀ ] Σ[ M ∶ Λ₀ ] N -↠ M
      qΛ = q-at-Λ .fst

      QΛ = HasTracker.F (q-at-Λ .snd)

      qQ-at-⊤ : Trackable ⊤ₐ (⊠ ⊤ₐ)
      qQ-at-⊤ = fun

      QΛ[M] : {N M : Λ₀} → N -↠ M → Lift (QΛ [ N ] -↠ ⌜ qΛ M .fst ⌝)
      QΛ[M] = HasTracker.F⊩f (q-at-Λ .snd) 

      QΛ-is-quoting : (M : Λ₀) → QΛ [ M ] -↠ ⌜ M ⌝
      QΛ-is-quoting M = let open -↠-Reasoning in begin
        QΛ [ M ]
          -↠⟨ lower (QΛ[M] -↠-refl) ⟩
        ⌜ qΛ M .fst ⌝
        ≡[ i ]⟨ ⌜ lem M i .fst  ⌝ ⟩
        ⌜ M ⌝ ∎
        where
          lem : (M : Λ₀) → qΛ M ≡ (M , M , _)
          lem M =
            let open ≡-Reasoning
                open HasTracker (*→Λ M .snd)
                s = F⊩f (snd (snd (qQ-at-⊤ .fst tt*))) in begin
              qΛ M
                ≡⟨ naturality (*→Λ M) _ ⟩
              (↑₁ M [ _ ] , M , s) 
                ≡[ i ]⟨ subst-rename-∅ _ M i , M , transport-filler (cong (_-↠ M) (subst-rename-∅ _ M)) s i ⟩ 
              (M , M , subst (_-↠ M) (subst-rename-∅ _ M) s) ∎

  forgetful : {X : Asm 𝓤₀} → Trackable (⊠ X) (⊠ Λ₀ₐ)
  forgetful = (λ { (M , _ , _) → M , M , -↠-refl }) , (0 , λ N-↠⌜M⌝ → N-↠⌜M⌝)

  Λ-map : {X Y : Asm 𝓤₀} → Trackable X Y → Trackable (⊠ Λ₀ₐ) (⊠ Λ₀ₐ)
  Λ-map (f , F , F⊩f) = (λ { (M , N , r) → F [ M ] , F [ N ] , reduce-ssubst F r }) ,
    ↑₁ Sub · (↑₁ ⌜ F ⌝) · 0 , λ { {M} {N , _ , _} (lift M-↠N) → lift (begin
      (↑₁ Sub · (↑₁ ⌜ F ⌝) · 0) [ M ]
        ≡⟨ refl ⟩
      (↑₁ Sub) [ M ] · (↑₁ ⌜ F ⌝) [ M ] · M
        ≡⟨ cong₂ (λ L N → L · N · M) (subst-rename-∅ _ Sub) (subst-rename-∅ _ ⌜ F ⌝) ⟩
      Sub · ⌜ F ⌝ · M
        -↠⟨ ·ᵣ-cong M-↠N ⟩
      Sub · ⌜ F ⌝ · ⌜ N ⌝
        -↠⟨ Sub-↠ ⟩
      ⌜ F [ N ] ⌝ ∎) }
      where
        open -↠-Reasoning
