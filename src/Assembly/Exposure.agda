{-# OPTIONS --without-K --cubical #-}

module Assembly.Exposure where

open import Prelude
  hiding (id; _∘_)
open import Calculus.SystemT
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
  □ (|X| , asmstr A _⊩_ _isRealisableₓ) = |□X| , asmstr nat _⊩□x_  _isRealisable
    where
    -- □ X consists of terms of type `nat` which reduces to a literal
    -- of a Gödel numbering, this reflects the fact that a well-typed
    -- metaprogram may produce a representation containing β-redexs.
      |□X| : (universe-of |X|) ̇
      |□X| =
        Σ[ n̅ ꞉ Prog nat ] Σ[ ▹x ꞉ ▹ |X| ] ▹[ α ] ∃[ M ꞉ Prog A ]
        -- n̅ -↠ ⌜ M ⌝ × M ⊩ ▹x α
        n̅ -↠ ⌜ M ⌝ × (Σ[ M′ ꞉ Prog A ] M -↠ M′ × M′ ⊩ ▹x α)

      _⊩□x_   : Prog nat → |□X| → _
      M′ ⊩□x (M , x , M⊩x) = Lift (M′ -↠ M)

      _isRealisable  : Π[ x ꞉ |□X| ] ∃[ M ꞉ Prog nat ] M ⊩□x x
      (M , x , M⊩x) isRealisable = ∣ M , lift -↠-refl ∣

  □map : Trackable X Y → Trackable (□ X) (□ Y)
  □map {X = X} {Y = Y} (f , F , F⊩f) = □f , □F , realisable
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)
      module □X = AsmStr (str (□ X))
      module □Y = AsmStr (str (□ Y))
      □f : ⟨ □ X ⟩ → ⟨ □ Y ⟩
      □f (n , ▹x , n⊩▹x) = Ap · ⌜ F ⌝ · n , ▹map f ▹x , λ α →
        let x = ▹x α
--            p : Σ[ M ꞉ Prog X.type ] n -↠ ⌜ M ⌝ × M X.⊩ x
--              → ∃[ N ꞉ Prog Y.type ] Ap · ⌜ F ⌝  · n -↠ ⌜ N ⌝ × N Y.⊩ f x
            p : Σ[ M ꞉ Prog X.type ] n -↠ ⌜ M ⌝ × (Σ[ M′ ꞉ Prog X.type ] M -↠ M′ × M′ X.⊩ x)
              → ∃[ N ꞉ Prog Y.type ] Ap · ⌜ F ⌝ · n -↠ ⌜ N ⌝ ×
                  (Σ[ N′ ꞉ Prog Y.type ] N -↠ N′ × N′ Y.⊩ f x) 
            p = λ {(M , n-↠⌜M⌝ , M′ , M-↠M′ , M′⊩x) →
              let P = F⊩f M′ x M′⊩x
                  N = P .fst
                  FM′-↠N = P .snd .fst
                  N⊩fx   = P .snd .snd
                  Ap⌜F⌝n-↠⌜FM⌝ = begin
                    Ap · ⌜ F ⌝ · n
                      -↠⟨ ·ᵣ-↠ n-↠⌜M⌝ ⟩
                    Ap · ⌜ F ⌝ · ⌜ M ⌝
                      -↠⟨ Ap-↠ ⟩
                    ⌜ F · M ⌝
                      ∎
                  FM-↠N = begin
                    F · M
                      -↠⟨ ·ᵣ-↠ M-↠M′ ⟩
                    F · M′
                      -↠⟨ FM′-↠N ⟩ 
                    N
                      ∎
              in ∣ F · M , Ap⌜F⌝n-↠⌜FM⌝ , N , FM-↠N , N⊩fx ∣}
        in rec propTruncIsProp p (n⊩▹x α)

      □F : Prog (nat `→ nat)
      □F = ƛ ↑ Ap · ↑ ⌜ F ⌝ · (# 0)

      realisable : Π[ M ꞉ Prog nat ] Π[ x ꞉ ⟨ □ X ⟩ ] (M □X.⊩ x → Σ[ N ꞉ Prog nat ] □F · M -↠ N × N □Y.⊩ □f x)
      realisable M (N , ▹x , p) (lift M-↠N) = Ap · ⌜ F ⌝ · N , red , lift -↠-refl
        where
          red : □F · M -↠ Ap · ⌜ F ⌝ · N
          red = begin
            □F · M
              -→⟨ β-ƛ· ⟩
            (↑ Ap) [ M ] · ↑ ⌜ F ⌝ [ M ] · M
              ≡⟨ cong₂ (λ N L → N · L · M) (subst-↑ _ Ap) (subst-↑ _ ⌜ F ⌝) ⟩
            Ap · ⌜ F ⌝ · M
              -↠⟨ ·ᵣ-↠ M-↠N ⟩
            Ap · ⌜ F ⌝ · N
              ∎
  
  -- Proposition. Every function |□ ⊥| → ⊥ gives rise to ▹ ⊥ → ⊥.
  bang : (⟨ □ ⊥ₐ {𝓤}⟩ → ⊥* {𝓤}) → ▹ ⊥* → ⊥*
  bang eval⊥ ▹x = eval⊥ (`zero , ▹x , λ α → ⊥*-elim (▹x α))

  -- Theorem. Evaluation □ ⊥ → ⊥ does not exist.
  eval-does-not-exist : Trackable {𝓤} (□ ⊥ₐ) ⊥ₐ → ⊥*
  eval-does-not-exist (e , hasTracker) = fix (bang e)

  -- quoting-does-not-exist : ({X : Asm 𝓤} → Trackable (𝔗 A) (□ 𝔗 A)) → ⊥
  -- quoting-does-not-exist = {!!}
