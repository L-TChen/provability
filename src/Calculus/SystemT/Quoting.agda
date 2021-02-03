{-# OPTIONS --without-K --cubical #-}

module Calculus.SystemT.Quoting where

open import Prelude 
  hiding (_≡⟨_⟩_; _∎; ⟪_⟫)

open import Calculus.SystemT.Base
open import Calculus.SystemT.Substitution

private
  variable
    Γ : Cxt
    A B C : 𝕋
    M N L : ∅ ⊢ A
    m n   : ∅ ⊢ ℕ̇

record Quoting : 𝓤₀ ̇ where
  field
    ⌜_⌝          : Prog A → Prog ℕ̇
    ⌜⌝-injective : ⌜ M ⌝ ≡ ⌜ M ⌝ → M ≡ N

    -- ⊢ □ (A → B) →̇ □ A →̇ □ B
    Ap   : Prog (ℕ̇ →̇ ℕ̇ →̇ ℕ̇)
    Ap-↠ : ∅ ⊢ Ap · ⌜ M ⌝ · ⌜ N ⌝ -↠ ⌜ M · N ⌝

    -- ⊢ □ A →̇ □ (□ A)
    Num   : Prog (ℕ̇ →̇ ℕ̇)
    Num-↠ : ∅ ⊢ Num · ⌜ M ⌝ -↠ ⌜ ⌜ M ⌝ ⌝

  open -↠-Reasoning
  -- ⊢ □ (ℕ →̇ A) →̇ □ A
  diag : Prog (ℕ̇ →̇ ℕ̇)
  diag = ƛ (↑ Ap) · # 0 · (↑ Num · # 0)

  diag-⌜⌝ : ∅ ⊢ diag · ⌜ M ⌝ -↠ ⌜ M · ⌜ M ⌝ ⌝
  diag-⌜⌝ {M = M} = begin
      diag · ⌜ M ⌝
    -→⟨ β-ƛ· ⟩
      ↑ Ap [ ⌜ M ⌝ ] · ⌜ M ⌝ · (↑ Num [ ⌜ M ⌝ ] · ⌜ M ⌝)
    ≡⟨ cong₂ (λ N L → N · ⌜ M ⌝ · (L · ⌜ M ⌝)) (subst-↑ _ Ap) (subst-↑ _ Num) ⟩
      Ap · ⌜ M ⌝ · (Num · ⌜ M ⌝)
    -↠⟨ ·ᵣ-↠ Num-↠ ⟩
      Ap · ⌜ M ⌝ · ⌜ ⌜ M ⌝ ⌝
    -↠⟨ Ap-↠ ⟩
      ⌜ M · ⌜ M ⌝ ⌝
    ∎

  -- the β-redex is for (∅ ⊢ igfix A · ⌜ M ⌝ -↠ ⌜ gfix M ⌝) to be true
  G : Prog (ℕ̇ →̇ A) → Prog (ℕ̇ →̇ A)
  G M = (ƛ ƛ # 1 · (↑ diag · # 0)) · M
  
  -- ⊢ □ A →̇ A   ⇒   ⊢ A
  gfix : Prog (ℕ̇ →̇ A) → Prog A
  gfix {A} M = G M · ⌜ G M ⌝

  gfix-spec : ∅ ⊢ gfix M -↠ M · ⌜ gfix M ⌝
  gfix-spec {A = A} {M = M} = begin
      G M · ⌜ G M ⌝
    -→⟨ ξ-·ₗ β-ƛ· ⟩
      (ƛ ↑₁ M · (↑ diag ⟪ _ ⟫ · # 0)) · ⌜ G M ⌝
    -→⟨ β-ƛ· ⟩
      rename S_ M ⟪ _ ⟫ · (↑ diag ⟪ _ ⟫ ⟪ _ ⟫ · ⌜ G M ⌝)
    ≡⟨ cong₂ (λ N L → N · (L · ⌜ G M ⌝)) (subst-rename-∅ S_ _ M) (subst-subst _ _ (↑ diag)) ⟩ 
      M · (↑ diag ⟪ _ ⟫ · ⌜ G M ⌝)
    ≡⟨ cong (λ N → M · (N · ⌜ G M ⌝)) (subst-↑ _ diag) ⟩
      M · (diag · ⌜ G M ⌝)
    -↠⟨ ·ᵣ-↠ diag-⌜⌝ ⟩
      M · ⌜ G M · ⌜ G M ⌝ ⌝
    ∎

  -- ⊢ □ (□ A →̇ A) →̇ □ A
  igfix : (A : 𝕋) → Prog (ℕ̇ →̇ ℕ̇)
  igfix A = ƛ ↑ diag · (↑ Ap · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · # 0)

  igfix-⌜⌝ : {M : ∅ ⊢ ℕ̇ →̇ A} → ∅ ⊢ igfix A · ⌜ M ⌝ -↠ ⌜ gfix M ⌝
  igfix-⌜⌝ {A = A} {M = M} = begin
      igfix A · ⌜ M ⌝
    -→⟨ β-ƛ· ⟩
      (↑ diag) ⟪ _ ⟫ · (↑ Ap ⟪ _ ⟫ · ↑ ⌜ ƛ ƛ (# 1 · (↑ diag · # 0)) ⌝  ⟪ _ ⟫ · ⌜ M ⌝)
    ≡⟨ {!!} ⟩ -- ≡⟨ (λ i → (subst-↑ _ diag i) · (subst-↑ _ Ap i · subst-↑ _ _ i · ⌜ M ⌝)) ⟩
      diag · (Ap · ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · ⌜ M ⌝)
    -↠⟨ ·ᵣ-↠ Ap-↠ ⟩
      diag · ⌜ g ⌝
    -↠⟨ diag-⌜⌝ ⟩
      ⌜ g · ⌜ g ⌝ ⌝
    ∎
    where
      g : ∅ ⊢ ℕ̇ →̇ A
      g = G M

  -- -- ⊢ □ A →̇ A   ⇒   ⊢ A →̇ A   ⇒   ⊢ A
  -- selfEval⇒fixpoint
  --   : Σ[ e ∈ ∅ ⊢ ℕ̇ →̇ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)
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
  --     f∘e : ∅ ⊢ ℕ̇ →̇ A
  --     f∘e = ƛ ↑ f · (↑ e · # 0)

  -- -- ¬ ∀ A. □ A → A
  -- ¬∃selfEval : (∀ A → Σ[ e ∈ ∅ ⊢ ℕ̇ →̇ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)) → ⊥
  -- ¬∃selfEval e with selfEval⇒fixpoint (e ℕ̇) (ƛ suc (# 0))
  -- ... | a , a-↠suca = {! !}

  -- rice
  --   : (d : ∅ ⊢ ℕ̇ →̇ ℕ̇) (a b : ∅ ⊢ A)
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
