{-# OPTIONS --without-K --cubical #-}

module Calculus.SystemT.Quoting where

open import Prelude 
  hiding (_≡⟨_⟩_; ≡⟨⟩-syntax; _∎; ⟪_⟫)

open import Calculus.SystemT.Base
open import Calculus.SystemT.Substitution
open import Calculus.SystemT.Confluence
 
private
  variable
    A B C : 𝕋
    M N F : ∅ ⊢ A
    m̅ n̅ l̅ : ∅ ⊢ nat

record Quoting : 𝓤₀ ̇ where
  field
    ⌜_⌝          : Prog A → Prog nat

    -- ⌜-⌝ reflects equality
    ⌜⌝-injective : ⌜ M ⌝ ≡ ⌜ N ⌝ → M ≡ N
    ⌜⌝-normal    : (M : Prog A) → Normal ⌜ M ⌝

    -- ⊢ □ (A → B) →̇ □ A →̇ □ B
    Ap   : Prog (nat →̇ nat →̇ nat)
    Ap-↠ : Ap · ⌜ M ⌝ · ⌜ N ⌝ -↠ ⌜ M · N ⌝

    -- ⊢ □ A →̇ □ (□ A)
    Num   : Prog (nat →̇ nat)
    Num-↠ : Num · ⌜ M ⌝ -↠ ⌜ ⌜ M ⌝ ⌝

  open -↠-Reasoning

  quoting-not-definable : ¬ (Σ[ Q ꞉ Prog (nat →̇ nat) ] Π[ M ꞉ Prog nat ] Q · M -↠ ⌜ M ⌝)
  quoting-not-definable (Q , QM=⌜M⌝) = 𝐼·M≢M (⌜⌝-injective ⌜I·M⌝=⌜M⌝)
    where
      QI0-↠⌜0⌝ : Q · (𝐼 nat · zero) -↠ ⌜ zero ⌝
      QI0-↠⌜0⌝ = begin
        Q · (𝐼 nat · zero)
          -→⟨ ξ-·ᵣ β-ƛ· ⟩
        Q · zero
          -↠⟨ QM=⌜M⌝ zero ⟩
        ⌜ zero ⌝ ∎

      ⌜I·M⌝=⌜M⌝ : ⌜ 𝐼 nat · zero ⌝ ≡ ⌜ zero ⌝
      ⌜I·M⌝=⌜M⌝ = Normal⇒Path (⌜⌝-normal (𝐼 nat · zero)) (⌜⌝-normal zero) (QM=⌜M⌝ (𝐼 nat · zero)) QI0-↠⌜0⌝

  -- ⊢ □ (ℕ →̇ A) →̇ □ A
  Diag : Γ ⊢ nat →̇ nat
  Diag = ƛ ↑ Ap · # 0 · (↑ Num · # 0)

  U : ∀ A → Prog ((nat →̇ A) →̇ nat →̇ A)
  U A = ƛ ƛ # 1 · (↑ Diag · # 0)

  -- the β-redex is for (∅ ⊢ igfix A · ⌜ M ⌝ -↠ ⌜ gfix M ⌝) to be true
  W : (A : 𝕋) → Prog (nat →̇ A) → Prog (nat →̇ A)
  W A F = U A · F

  Diag-↠ : Diag · ⌜ M ⌝ -↠ ⌜ M · ⌜ M ⌝ ⌝
  Diag-↠ {M = M} = begin
      Diag · ⌜ M ⌝
    -→⟨ β-ƛ· ⟩
      ↑ Ap [ ⌜ M ⌝ ] · ⌜ M ⌝ · (↑ Num [ ⌜ M ⌝ ] · ⌜ M ⌝)
    ≡⟨ cong₂ (λ N L → N · ⌜ M ⌝ · (L · ⌜ M ⌝)) (subst-↑ _ Ap) (subst-↑ _ Num) ⟩
      Ap · ⌜ M ⌝ · (Num · ⌜ M ⌝)
    -↠⟨ ·ᵣ-↠ Num-↠ ⟩
      Ap · ⌜ M ⌝ · ⌜ ⌜ M ⌝ ⌝
    -↠⟨ Ap-↠ ⟩
      ⌜ M · ⌜ M ⌝ ⌝
    ∎
  
  -- ⊢ □ A →̇ A   ⇒   ⊢ A
  gfix : Prog (nat →̇ A) → Prog A
  gfix F = Wₘ · ⌜ Wₘ ⌝
    where
      Wₘ = W _ F

  gfix-↠ : gfix F -↠ F · ⌜ gfix F ⌝
  gfix-↠ {F = F} = begin
      Wₘ · ⌜ Wₘ ⌝
    -→⟨ ξ-·ₗ β-ƛ· ⟩
      (ƛ ↑₁ F · (↑ Diag ⟪ _ ⟫ · # 0)) · ⌜ Wₘ ⌝
    -→⟨ β-ƛ· ⟩
      ↑₁ F [ ⌜ Wₘ ⌝ ] · (↑ Diag ⟪ _ ⟫ [ ⌜ Wₘ ⌝ ] · ⌜ Wₘ ⌝)
    ≡⟨ cong₂ (λ N L → N · (L · ⌜ Wₘ ⌝)) (subst-rename-∅ S_ _ F) (subst-subst _ _ (↑ Diag)) ⟩ 
      F · (↑ Diag ⟪ _ ⟫ · ⌜ Wₘ ⌝)
    ≡⟨ cong (λ M → F · (M · ⌜ Wₘ ⌝)) (subst-↑ _ Diag) ⟩
      F · (Diag · ⌜ Wₘ ⌝)
    -↠⟨ ·ᵣ-↠ Diag-↠ ⟩
      F · ⌜ Wₘ · ⌜ Wₘ ⌝ ⌝
    ∎
    where
      Wₘ = W _ F

  -- ⊢ □ (□ A →̇ A) →̇ □ A
  igfix : (A : 𝕋) → Prog (nat →̇ nat)
  igfix A = ƛ ↑ Diag · (↑ Ap · ↑ ⌜ U A ⌝ · # 0)

  igfix-⌜⌝ : (A : 𝕋) → (M : ∅ ⊢ nat →̇ A)
    → igfix A · ⌜ M ⌝ -↠ ⌜ gfix M ⌝
  igfix-⌜⌝ A M = begin
      igfix A · ⌜M⌝
    -→⟨ β-ƛ· ⟩
      (↑ Diag) [ ⌜M⌝ ] · (↑ Ap [ ⌜M⌝ ] · ↑ ⌜ U A ⌝ [ ⌜M⌝ ] · ⌜M⌝)
    ≡[ i ]⟨ subst-↑ (subst-zero ⌜M⌝) Diag i · (subst-↑ (subst-zero ⌜M⌝) Ap i · subst-↑ (subst-zero ⌜M⌝) ⌜ U A ⌝ i · ⌜M⌝) ⟩
      Diag · (Ap · ⌜ U A ⌝ · ⌜M⌝)
    -↠⟨ ·ᵣ-↠ Ap-↠ ⟩
      Diag · ⌜ Wₘ ⌝
    -↠⟨ Diag-↠ ⟩
      ⌜ Wₘ · ⌜ Wₘ ⌝ ⌝
    ∎
    where
      Wₘ : ∅ ⊢ nat →̇ A
      Wₘ = W A M
      ⌜M⌝ = ⌜ M ⌝ 

  -- -- ⊢ □ A →̇ A   ⇒   ⊢ A →̇ A   ⇒   ⊢ A
  -- selfEval⇒fixpoint
  --   : Σ[ e ∈ ∅ ⊢ nat →̇ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)
  --   → (f : ∅ ⊢ A →̇ A)
  --   → Σ[ a ∈ ∅ ⊢ A ] (∅ ⊢ a -↠ f · a)
  -- selfEval⇒fixpoint {A = A} (e , e-⌜⌝-id) f = gfix f∘e ,
  --   (begin
  --     gfix f∘e
  --   -↠⟨ gfix-spec ⟩
  --     f∘e · ⌜ gfix f∘e ⌝
  --   -→⟨ β-ƛ· ⟩
  --     ↑ f ⟪ _ ⟫ · (↑ e ⟪ _ ⟫ · ⌜ gfix f∘e ⌝)
  --   ≡⟨ P.cong₂ (λ M N → M · (N · ⌜ gfix (ƛ ↑ f · (↑ e · # 0)) ⌝)) (subst-↑ _ f) (subst-↑ _ e) ⟩
  --     f · (e · ⌜ gfix f∘e ⌝)
  --   -↠⟨ ·₂-↠ (e-⌜⌝-id (gfix f∘e))  ⟩
  --     f · gfix (f∘e)
  --   ∎)
  --   where
  --     open -↠-Reasoning
  --     f∘e : ∅ ⊢ nat →̇ A
  --     f∘e = ƛ ↑ f · (↑ e · # 0)

  -- -- ¬ ∀ A. □ A → A
  -- ¬∃selfEval : (∀ A → Σ[ e ∈ ∅ ⊢ nat →̇ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)) → ⊥
  -- ¬∃selfEval e with selfEval⇒fixpoint (e nat) (ƛ suc (# 0))
  -- ... | a , a-↠suca = {! !}

  -- rice
  --   : (d : ∅ ⊢ nat →̇ nat) (a b : ∅ ⊢ A)
  --   → ((x y : ∅ ⊢ A) → ∅ ⊢ x -↠ y → ∅ ⊢ d · ⌜ x ⌝ -↠ d · ⌜ y ⌝)
  --   → ∅ ⊢ d · ⌜ a ⌝ -↠ zero
  --   → ∅ ⊢ d · ⌜ b ⌝ -↠ (suc zero)
  --   → ⊥
  -- rice d a b d-ext da-↠0 db-↠1 = {! d · gfix (ƛ n → ) !} where
  --   -- r = λ n. if d n then a else b
  --   -- gnum r = gnum (λ x y n. if d n then x else y) `app` ()
  --   --    d (gfix r)
  --   -- -↠ d (gnum (r · (gfix r))
  --   -- -↠ d (gnum (if d (gfix r) then a else b))
  --   -- -↠ { d ⌜ a ⌝ -↠ 0   if d (gfix r) -↠ 1
  --   --    ; d (gnum b) -↠ 1   if d (gfix r) -↠ 0
