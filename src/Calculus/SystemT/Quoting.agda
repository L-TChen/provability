{-# OPTIONS --without-K --cubical #-}

module Calculus.SystemT.Quoting where

open import Prelude 

open import Calculus.SystemT.Base

private
  variable
    Γ : Cxt
    A B C : 𝕋
    a b c : ∅ ⊢ A
    m n   : ∅ ⊢ ℕ̇

record Quoting : 𝓤₀ ̇ where
  field
    ⌜_⌝          : ∅ ⊢ A → ∅ ⊢ ℕ̇
    ⌜⌝-injective : ⌜ a ⌝ ≡ ⌜ b ⌝ → a ≡ b

    -- ⊢ □ (A → B) →̇ □ A →̇ □ B
    Ap   : ∅ ⊢ ℕ̇ →̇ ℕ̇ →̇ ℕ̇
    Ap-↠ : ∅ ⊢ Ap · ⌜ a ⌝ · ⌜ b ⌝ -↠ ⌜ a · b ⌝

    -- ⊢ □ A →̇ □ (□ A)
    Num   : ∅ ⊢ ℕ̇ →̇ ℕ̇
    Num-↠ : ∅ ⊢ Num · ⌜ a ⌝ -↠ ⌜ ⌜ a ⌝ ⌝

  -- ⊢ □ (ℕ →̇ A) →̇ □ A
  diag : ∅ ⊢ ℕ̇ →̇ ℕ̇
  diag = ƛ (↑ Ap) · # 0 · (↑ Num · # 0)

  -- diag-⌜⌝ : ∅ ⊢ diag · ⌜ a ⌝ -↠ ⌜ a · ⌜ a ⌝ ⌝
  -- diag-⌜⌝ {a = a} =
  --   begin
  --     diag · ⌜ a ⌝
  --   -→⟨ β-ƛ· ⟩
  --     ↑ app ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝ · (↑ ignum ⟪ subst-zero ⌜ a ⌝ ⟫ · ⌜ a ⌝)
  --   ≡⟨ P.cong₂ (λ M N → M · ⌜ a ⌝ · (N · ⌜ a ⌝)) (subst-↑ _ app) (subst-↑ _ ignum) ⟩
  --     app · ⌜ a ⌝ · (ignum · ⌜ a ⌝)
  --   -↠⟨ ·₂-↠ ignum-⌜⌝ ⟩
  --     app · ⌜ a ⌝ · ⌜ ⌜ a ⌝ ⌝
  --   -↠⟨ app-⌜⌝-⌜⌝ ⟩
  --     ⌜ a · ⌜ a ⌝ ⌝
  --   ∎
  --   where open -↠-Reasoning

  -- -- ⊢ □ A →̇ A   ⇒   ⊢ A
  -- gfix : ∅ ⊢ ℕ̇ →̇ A → ∅ ⊢ A
  -- gfix {A} a = g · ⌜ g ⌝ where
  --   -- the β-redex is for (∅ ⊢ igfix A · ⌜ a ⌝ -↠ ⌜ gfix a ⌝) to be true
  --   g : ∅ ⊢ ℕ̇ →̇ A
  --   g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a

  -- gfix-spec : ∅ ⊢ gfix a -↠ a · ⌜ gfix a ⌝
  -- gfix-spec {A = A} {a = a} =
  --   begin
  --     g · ⌜ g ⌝
  --   -→⟨ ξ-·₁ β-ƛ· ⟩
  --     ƛ_ {B = A} (rename S_ a · (↑ diag ⟪ _ ⟫ · # 0)) · ⌜ g ⌝
  --   -→⟨ β-ƛ· ⟩
  --     rename S_ a ⟪ _ ⟫ · (↑ diag ⟪ _ ⟫ ⟪ _ ⟫ · ⌜ g ⌝)
  --   ≡⟨ P.cong₂ (λ M N → M · (N · ⌜ g ⌝)) (subst-rename-∅ S_ _ a) (subst-subst _ _ (↑ diag)) ⟩
  --     a · (↑ diag ⟪ _ ⟫ · ⌜ g ⌝)
  --   ≡⟨ P.cong (λ M → a · (M · ⌜ g ⌝)) (subst-↑ _ diag) ⟩
  --     a · (diag · ⌜ g ⌝)
  --   -↠⟨ ·₂-↠ diag-⌜⌝ ⟩
  --     a · ⌜ g · ⌜ g ⌝ ⌝
  --   ∎
  --   where
  --     open -↠-Reasoning
  --     g : ∅ ⊢ ℕ̇ →̇ A
  --     g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a

  -- -- ⊢ □ (□ A →̇ A) →̇ □ A
  -- igfix : (A : Type) → ∅ ⊢ ℕ̇ →̇ ℕ̇
  -- igfix A = ƛ ↑ diag · (↑ app · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · # 0)

  -- igfix-⌜⌝ : {a : ∅ ⊢ ℕ̇ →̇ A} → ∅ ⊢ igfix A · ⌜ a ⌝ -↠ ⌜ gfix a ⌝
  -- igfix-⌜⌝ {A = A} {a = a} =
  --   begin
  --     igfix A · ⌜ a ⌝
  --   -→⟨ β-ƛ· ⟩
  --     (↑ diag) ⟪ _ ⟫ · (↑ app ⟪ _ ⟫ · ↑ ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝  ⟪ _ ⟫ · ⌜ a ⌝)
  --   ≡⟨ cong₃ (λ L M N → L · (M · N · ⌜ a ⌝)) (subst-↑ _ diag) (subst-↑ _ app) (subst-↑ _ _) ⟩
  --     diag · (app · ⌜ ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0)) ⌝ · ⌜ a ⌝)
  --   -↠⟨ ·₂-↠ app-⌜⌝-⌜⌝ ⟩
  --     diag · ⌜ g ⌝
  --   -↠⟨ diag-§⌜⌝ ⟩
  --     ⌜ g · ⌜ g ⌝ ⌝
  --   ∎
  --   where
  --     open -↠-Reasoning
  --     g : ∅ ⊢ ℕ̇ →̇ A
  --     g = (ƛ ƛ_ {B = A} (# 1 · (↑ diag · # 0))) · a
  --     cong₃ : ∀ f {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
  --     cong₃ f P.refl P.refl P.refl = P.refl

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
