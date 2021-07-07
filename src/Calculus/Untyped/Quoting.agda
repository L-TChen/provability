module Calculus.Untyped.Quoting where

open import Prelude

open import Calculus.Untyped.Base
open import Calculus.Untyped.Progress
  using (Normal)
open import Calculus.Untyped.Combinators
open import Calculus.Untyped.Substitution
open import Calculus.Untyped.Confluence

private
  variable
    m n l : ℕ
    L M N F : Λ n

record Quoting : 𝓤₀ ̇ where
  field
    ⌜_⌝          : Λ n → Λ₀

    -- ⌜-⌝ reflects equality
    ⌜⌝-injective : ⌜ M ⌝ ≡ ⌜ N ⌝ → M ≡ N
    ⌜⌝-normal    : Normal ⌜ M ⌝

    -- ⊢ □ (A → B) ⇒ □ A ⇒ □ B
    App    : Λ 2
    App-↠  : App ⟪ exts (subst-zero ⌜ M ⌝) ⟫ [ ⌜ N ⌝ ] -↠ ⌜ M · N ⌝
    -- Sub : Λ₀
    Sub   : Λ₀
    Sub-↠ : Sub · ⌜ M ⌝ · ⌜ N ⌝ -↠ ⌜ M [ N ] ⌝

    -- ⊢ □ A `→ □ (□ A)
    Quote   : Λ₁
    Quote-↠ : Quote [ ⌜ M ⌝ ] -↠ ⌜ ⌜ M ⌝ ⌝

    Eval : Λ₁
    Eval-↠ : Eval [ ⌜ M ⌝ ] -↠ M

  open -↠-Reasoning
  -- ⊢ □ A `→ □ (□ A)
  Ap : Λ₀
  Ap = ƛ ƛ App
  Ap-↠ : Ap · ⌜ M ⌝ · ⌜ N ⌝ -↠ ⌜ M · N ⌝
  Ap-↠ {_} {M} {N} = begin
    Ap · ⌜ M ⌝ · ⌜ N ⌝
      -→⟨ ξₗ β ⟩
    (ƛ App) [ ⌜ M ⌝ ] · ⌜ N ⌝
      -→⟨ β ⟩
    App ⟪ exts (subst-zero ⌜ M ⌝) ⟫ [ ⌜ N ⌝ ]
      -↠⟨ App-↠ ⟩
    ⌜ M · N ⌝ ∎ 

  Num : Λ₀
  Num = ƛ Quote

  Num-↠ : Num · ⌜ M ⌝ -↠ ⌜ ⌜ M ⌝ ⌝
  Num-↠ {M = M} = begin
    Num · ⌜ M ⌝
      -→⟨ β ⟩
    Quote [ ⌜ M ⌝ ]
      -↠⟨ Quote-↠ ⟩
    ⌜ ⌜ M ⌝ ⌝ ∎

  I·I≠I : 𝑰 · 𝑰 ≢ 𝑰
  I·I≠I = encode

  quoting′-not-definable : ¬ (Σ[ Q ∶ Λ₁ ] Π[ M ∶ Λ₀ ] Q [ M ] -↠ ⌜ M ⌝ )
  quoting′-not-definable (Q , QM-↠⌜M⌝) = I·I≠I (⌜⌝-injective (Normal⇒Path ⌜⌝-normal ⌜⌝-normal (QM-↠⌜M⌝ (𝑰 · 𝑰)) QII-↠⌜I⌝))
    where
      QII-↠⌜I⌝ : Q [ 𝑰 · 𝑰 ] -↠ ⌜ 𝑰 ⌝
      QII-↠⌜I⌝ = begin
        Q [ 𝑰 · 𝑰 ]
          -↠⟨ reduce-ssubst Q (-→to-↠ β) ⟩
        Q [ 𝑰 ]
          -↠⟨ QM-↠⌜M⌝ 𝑰 ⟩
        ⌜ 𝑰 ⌝ ∎

  -- ⊢ □ (ℕ `→ A) `→ □ A
  Diag : Λ₀
  Diag = ƛ ↑ Ap · 0 · (↑ Num · 0)

  Diag-↠ : Diag · ⌜ M ⌝ -↠ ⌜ M · ⌜ M ⌝ ⌝
  Diag-↠ {M = M} = begin
      Diag · ⌜ M ⌝
    -→⟨ β ⟩
      ↑ Ap [ ⌜ M ⌝ ] · ⌜ M ⌝ · (↑ Num [ ⌜ M ⌝ ] · ⌜ M ⌝)
    ≡⟨ cong₂ (λ N L → N · ⌜ M ⌝ · (L · ⌜ M ⌝)) (subst-rename-∅ _ Ap) (subst-rename-∅ _ Num) ⟩
      Ap · ⌜ M ⌝ · (Num · ⌜ M ⌝)
    -↠⟨ ·ᵣ-cong Num-↠ ⟩
      Ap · ⌜ M ⌝ · ⌜ ⌜ M ⌝ ⌝
    -↠⟨ Ap-↠ ⟩
      ⌜ M · ⌜ M ⌝ ⌝ ∎

  U : Λ₀
  U = ƛ ƛ 1 · (↑ Diag · 0)

  -- the β-redex is for (∅ ⊢ igfix A · ⌜ M ⌝ -↠ ⌜ gfix M ⌝) to be true
  W : Λ₀ → Λ₀
  W F = U · F
  -- ⊢ □ A `→ A   `→   ⊢ A

  gfix : Λ₀ → Λ₀
  gfix F = W F · ⌜ W F ⌝

  gfix-↠ : gfix F -↠ F · ⌜ gfix F ⌝
  gfix-↠ {F = F} = begin
      W F · ⌜ W F ⌝
    -→⟨ ξₗ β ⟩
      (ƛ ↑ F · (↑ Diag ⟪ _ ⟫ · 0)) · ⌜ W F ⌝
    -→⟨ β ⟩
      ↑ F [ ⌜ W F ⌝ ] · (↑ Diag ⟪ _ ⟫ [ ⌜ W F ⌝ ] · ⌜ W F ⌝)
    ≡⟨ cong₂ _·_ (subst-rename-∅ _ F) (cong (_· ⌜ W F ⌝) (subst-assoc _ _ (↑ Diag) ∙ subst-rename-∅ _ Diag)) ⟩ 
      F · (Diag · ⌜ W F ⌝)
    -↠⟨ ·ᵣ-cong Diag-↠ ⟩
      F · ⌜ W F · ⌜ W F ⌝ ⌝ ∎

  sfix : Λ₁ → Λ₀
  sfix F = gfix (ƛ F)

  sfix-↠ : sfix F -↠ F [ ⌜ sfix F ⌝ ]
  sfix-↠ {F = F} = begin
    sfix F
      -↠⟨ gfix-↠ ⟩
    (ƛ F) · ⌜ gfix (ƛ F) ⌝ 
      -→⟨ β ⟩
    F [ ⌜ sfix F ⌝ ]
      ∎
  igfix : Λ₁
  igfix = ↑ Diag · (↑ Ap · ↑ ⌜ U ⌝ · 0)

  igfix-↠ : {M : Λ₀} → igfix [ ⌜ M ⌝ ] -↠ ⌜ gfix M ⌝
  igfix-↠ {M} = begin
    ↑ Diag [ ⌜ M ⌝ ] · (↑ Ap [ ⌜ M ⌝ ] · ↑ ⌜ U ⌝ [ ⌜ M ⌝ ] · ⌜ M ⌝)  
      ≡⟨ cong₂ _·_ (subst-rename-∅ _ Diag) (cong (_· ⌜ M ⌝) (cong₂ _·_ (subst-rename-∅ _ Ap) (subst-rename-∅ _ ⌜ U ⌝))) ⟩
    Diag · (Ap · ⌜ U ⌝ · ⌜ M ⌝)  
      -↠⟨ ·ᵣ-cong Ap-↠  ⟩
    Diag · ⌜ W M ⌝
      -↠⟨ Diag-↠ ⟩
    ⌜ W M · ⌜ W M ⌝ ⌝ ∎

  -- -- ⊢ □ A `→ A   `→   ⊢ A `→ A   `→   ⊢ A
  -- selfEval`→fixpoint
  --   : Σ[ e ∈ ∅ ⊢ nat `→ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)
  --   → (f : ∅ ⊢ A `→ A)
  --   → Σ[ a ∈ ∅ ⊢ A ] (∅ ⊢ a -↠ f · a)
  -- selfEval`→fixpoint {A = A} (e , e-⌜⌝-id) f = gfix f∘e ,
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
  --     f∘e : ∅ ⊢ nat `→ A
  --     f∘e = ƛ ↑ f · (↑ e · # 0)

  -- -- ¬ ∀ A. □ A → A
  -- ¬∃selfEval : (∀ A → Σ[ e ∈ ∅ ⊢ nat `→ A ] (∀ a → ∅ ⊢ e · ⌜ a ⌝ -↠ a)) → ⊥
  -- ¬∃selfEval e with selfEval`→fixpoint (e nat) (ƛ suc (# 0))
  -- ... | a , a-↠suca = {! !}

  -- rice
  --   : (d : ∅ ⊢ nat `→ nat) (a b : ∅ ⊢ A)
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

