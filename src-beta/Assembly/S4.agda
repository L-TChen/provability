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
    X Y Z : ASM 𝓤

module _ (Q : Quoting) where
  open Quoting Q

  ⊠_ : ASM 𝓤 → ASM 𝓤
  ⊠_ {𝓤} (|X| , _⊩_ , ⊩-is-realisability) = |⊠X| , _⊩⊠X_ , record
    { ⊩-respects-↠ = λ {x} {x′} {y} → ⊩⊠X-respect-↠ {x} {x′} {y}
    ; ⊩-right-total = ⊩⊠X-right-total
    }
    where
      |⊠X| : 𝓤 ̇
      |⊠X| = Σ[ M ꞉ Λ₀ ] Σ[ x ꞉ |X| ] M ⊩ x
      -- Can we remove truncation? Yes.

      _⊩⊠X_ : (M : Λ₀) → |⊠X| → 𝓤 ̇
      n̅ ⊩⊠X (M , _ , _) = Lift (n̅ -↠ ⌜ M ⌝)

      ⊩⊠X-respect-↠ : _⊩⊠X_ respects _-↠_ on-the-left
      ⊩⊠X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩⊠X-right-total :  _⊩⊠X_ IsRightTotal
      ⊩⊠X-right-total (M , _ , M⫣x) = ∣ ⌜ M ⌝ , lift (⌜ M ⌝ _-↠_.∎) ∣

  ⊠map₀ : Trackable X Y → ⟨ ⊠ X ⟩ → ⟨ ⊠ Y ⟩
  ⊠map₀ (f , F , F⊩f) (M , x , M⊩x) = F [ M ] , f x , F⊩f M⊩x

  ⊠map₁ : Λ₁ → Λ₁
  ⊠map₁ F = ↑₁ Sub · ↑₁ ⌜ F ⌝ · 0

  ⊠map : Trackable X Y → Trackable (⊠ X) (⊠ Y)
  ⊠map {𝓤} {X} {Y} Ff@(f , F , f⫣F) = ⊠map₀ Ff , ⊠map₁ F , 
    λ {M} {x} → ⊠F⊩⊠f {M} {x}
    where
      open -↠-Reasoning
      ⊠F⊩⊠f : Tracks (⊠ X) (⊠ Y) (⊠map₁ F) (⊠map₀ Ff)
      ⊠F⊩⊠f {n̅} {M , _ , _} (lift n̅-↠⌜M⌝) = lift (begin
        ↑₁ Sub [ n̅ ] · ↑₁ ⌜ F ⌝ [ n̅ ] · n̅
          ≡[ i ]⟨ subst-rename-∅ {ρ = S_} (subst-zero n̅) Sub i · subst-rename-∅ {ρ = S_} (subst-zero n̅) ⌜ F ⌝ i · n̅ ⟩
        Sub · ⌜ F ⌝ · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        Sub · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Sub-↠ ⟩
        ⌜ F [ M ] ⌝ ∎)

  ⊠id=id : (X : ASM 𝓤) → (x : ⟨ ⊠ X ⟩) → ⊠map₀ (id X) x ≡ x
  ⊠id=id X x = refl

  ⊠gf=⊠g⊠f : (f : Trackable X Y) (g : Trackable Y Z) → (x : ⟨ ⊠ X ⟩) → ⊠map₀ (g ∘ f) x ≡ ⊠map₀ g (⊠map₀ f x)
  ⊠gf=⊠g⊠f {Z = Z} (f , F , F⊩f) (g , G , G⊩g) (M , x , r) i =
    G[F[M]]=G[F][M] i , g (f x) , transport-filler (cong (Z._⊩ g (f x)) (G[F[M]]=G[F][M] ⁻¹)) (G⊩g (F⊩f r)) (~ i)
    where
      module Z = AsmStr (str Z)
      G[F[M]]=G[F][M] = ∘-ssubst-ssubst G F M
      
  ⊠reflects∼ : (f g : Trackable X Y)
    → isSet ⟨ Y ⟩
    → ⊠map f ∼ ⊠map g ꞉ ⊠ X →ₐ ⊠ Y
    → f ∼ g ꞉ X →ₐ Y
  ⊠reflects∼ {X = X} f g YisSet ⊠f=⊠g x = rec (YisSet _ _)
    (λ { (M , M⊩x) → cong (λ x → fst (snd x)) (⊠f=⊠g (M , x , M⊩x))  })
    (X.⊩-right-total x)
    where
      module X = AsmStr (str X)

  ⊠-isExposure : IsExposure {𝓤} ⊠_  ⊠map
  ⊠-isExposure = record
    { preserve-id   = ⊠id=id
    ; preserve-comp = ⊠gf=⊠g⊠f
    ; reflects-∼    = {!!} -- ⊠reflects∼
    }

  ⊠-exposure : Exposure 𝓤
  ⊠-exposure = exposure ⊠_ ⊠map ⊠-isExposure
  
{-
  ⊠F=⊠G→F=G : (F G : Λ₁) → ⊠map₁ F ≡ ⊠map₁ G → F ≡ G
  ⊠F=⊠G→F=G F G ⊠F=⊠G = ⌜⌝-injective (↑ₗ-injective (decode (encode ⊠F=⊠G .fst .snd)))
    where
      postulate ↑ₗ-injective : {Γ Δ : Cxt} {A : 𝕋} {M N : Δ ⊢ A} → ↑ₗ_ {Δ} {_} {Γ} M ≡ ↑ₗ N → M ≡ N
-}
  eval : Trackable (⊠ X) X
  eval {X = X} = (λ x → fst (snd x)) , Eval ,
    λ { {N} {M , x , M⊩x} N-↠⌜M⌝ →
      X.⊩-respects-↠ (reduce-ssubst Eval (lower N-↠⌜M⌝)) ((X.⊩-respects-↠ Eval-↠ M⊩x)) }
    where
      module X  = AsmStr (str X)
      module ⊠X = AsmStr (str (⊠ X))

  eval-nat : NaturalTransformation {𝓤} ⊠-exposure Id
  eval-nat = eval , λ f x → refl

  quoting : Trackable (⊠ X) (⊠ ⊠ X)
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

      qΛ : Λ₀ → Σ[ N ꞉ Λ₀ ] Σ[ M ꞉ Λ₀ ] N -↠ M
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

  forgetful : {X : ASM 𝓤₀} → Trackable (⊠ X) (⊠ Λ₀ₐ)
  forgetful = (λ { (M , _ , _) → M , M , -↠-refl }) , (0 , λ N-↠⌜M⌝ → N-↠⌜M⌝)

  Λ-map : Trackable X Y → Trackable Λ₀ₐ Λ₀ₐ
  Λ-map (f , F , F⊩f) = F [_] , F , λ {M} {N} r → reduce-ssubst F r
