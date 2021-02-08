{-# OPTIONS --without-K --cubical #-}

module Assembly.Exposure where

open import Prelude
  hiding (id; _∘_)
open import Calculus.Untyped
open import Assembly.Base

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Endo-exposure

record IsEndoExposure (Q : Asm 𝓤 → Asm 𝓤) : 𝓤 ⁺ ̇ where 
  constructor is-exposure
  field
    map           : Trackable X Y → Trackable (Q X) (Q Y)
    preserve-id   : map id ∼ id ꞉ Q X →ₐ Q X
    preserve-comp : {f : Trackable X Y} {g : Trackable Y Z}
      → map g ∘ map f ∼ map (g ∘ f) ꞉ Q X →ₐ Q Z
    reflects-∼    : {f g : Trackable X Y}
      → map f ∼ map g ꞉ Q X →ₐ Q Y
      →     f ∼ g     ꞉ X   →ₐ Y

record EndoExposure : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    Q          : Asm 𝓤 → Asm 𝓤
    isExposure : IsEndoExposure Q

module _ (Q : Quoting) where
  open Quoting Q
  open -↠-Reasoning

  □_ : Asm 𝓤 → Asm 𝓤
  □_ {𝓤} X@(|X| , _⊩_ , ⊩-realisability) = |□X| , _⊩□X_ , is⊩ ? ⊩□X-right-total
    where
      module X = IsRealisability ⊩-realisability
      |□X| : 𝓤 ̇
      |□X| = Σ[ M ꞉ Λ₀ ] Σ[ ▹x ꞉ ▹ |X| ] ▹[ α ] M ⊩ ▹x α

      _⊩□X_ : (M : Λ₀) → |□X| → 𝓤 ̇
      n̅ ⊩□X (M , ▹x , M⊩▹x) = Lift (n̅ -↠ ⌜ M ⌝)

      ⊩□X-respect-↠ : _⊩□X_ respects _-↠_ on-the-left
      ⊩□X-respect-↠ M-↠N (lift N-↠⌜L⌝) = lift (-↠-trans M-↠N N-↠⌜L⌝)
      
      ⊩□X-right-total : IsRightTotal _⊩□X_
      ⊩□X-right-total (M , ▹x , M⊩x) = ∣ ⌜ M ⌝ , lift -↠-refl ∣

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {𝓤} {X} {Y} (f , hastracker {F} F⊩f) = □f , hastracker (□F⊩□f {{!!}} {{!!}})
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)
      module □X = AsmStr (str (□ X))
      module □Y = AsmStr (str (□ Y))
      □f : ⟨ □ X ⟩ → ⟨ □ Y ⟩
      □f (M , ▹x , M⊩x) = F · M , ▹map f ▹x , λ α → F⊩f (M⊩x α)

      □F : Λ₀
      □F = ƛ ↑ Ap · ↑ ⌜ F ⌝ · (# 0) 

      □F⊩□f : Tracks (□ X) (□ Y) □F □f
      □F⊩□f {n̅} {M , ▹x , M⊩x} (lift n̅-↠⌜M⌝) = lift (begin
        (ƛ ↑ Ap · ↑ ⌜ F ⌝ · # 0) · n̅
          -→⟨ β ⟩
        ↑ Ap [ n̅ ] · ↑ ⌜ F ⌝ [ n̅ ] · n̅
          -↠⟨ ·ᵣ-cong n̅-↠⌜M⌝ ⟩
        ↑ Ap [ n̅ ] · ↑ ⌜ F ⌝ [ n̅ ] · ⌜ M ⌝
          ≡⟨ {!!} ⟩
        Ap · ⌜ F ⌝ · ⌜ M ⌝
          -↠⟨ Ap-↠ ⟩
        ⌜ F · M ⌝ 
          ∎)

  -- -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (𝑰 , ▹x , λ α → ⊥*-elim (▹x α))

  -- -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
