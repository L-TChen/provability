{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Substitution where

open import Prelude
open import Calculus.Untyped.Base

private
  variable
    A B C   : 𝕋
    Γ Δ Ξ   : Cxt
    ρ ρ₁ ρ₂ : Rename Γ Δ
    σ σ₁ σ₂ : Subst Γ Δ

infixr 5 _⨟_

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
(σ ⨟ τ) x = σ x ⟪ τ ⟫

ids : Subst Γ Γ
ids = `_

----------------------------------------------------------------------
-- Congruence rules

subst-cong
  : ({A : 𝕋} (x : A ∈ Γ) → σ₁ x ≡ σ₂ x)
  → (M : Γ ⊢ A)
  → M ⟪ σ₁ ⟫ ≡ M ⟪ σ₂ ⟫
subst-cong p M i = M ⟪ funExt p i ⟫

----------------------------------------------------------------------
-- Properties of ext

ext-comp : (ρ₁ : Rename Γ Δ) (ρ₂ : Rename Δ Ξ)
  → (x : A ∈ B , Γ)
  → (ext ρ₂ ∘ ext ρ₁) x ≡ ext (ρ₂ ∘ ρ₁) x
ext-comp ρ₁ ρ₂ (Z _) = refl
ext-comp ρ₁ ρ₂ (S x) = refl

----------------------------------------------------------------------
-- Properties of Rename

ren : Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ

rename=subst-ren
  : (M : Γ ⊢ A)
  → rename ρ M ≡ M ⟪ ren ρ ⟫
rename=subst-ren (` x)      = refl
rename=subst-ren (M · N)    =
  cong₂ _·_ (rename=subst-ren M) (rename=subst-ren N)
rename=subst-ren {ρ = ρ} (ƛ M) =
  rename ρ (ƛ M)
    ≡⟨⟩
  ƛ rename (ext ρ) M
    ≡⟨ cong ƛ_ (rename=subst-ren M) ⟩
  ƛ M ⟪ ren (ext ρ) ⟫
    ≡[ i ]⟨ ƛ M ⟪ funExt (ren-ext ρ) i ⟫ ⟩
  ƛ M ⟪ exts (ren ρ) ⟫
    ≡⟨⟩
  (ƛ M) ⟪ ren ρ ⟫ ∎
  where
    open ≡-Reasoning
    ren-ext : (ρ : Rename Γ Δ)
      → ∀ {B} (x : B ∈ A , Γ) → ren (ext ρ) x ≡ exts (ren ρ) x
    ren-ext ρ (Z _) = refl
    ren-ext ρ (S x) = refl

rename-comp
  : (ρ₁ : Rename Γ Δ) (ρ₂ : Rename Δ Ξ)
  → {M : Γ ⊢ A}
  → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M
rename-comp ρ₁ ρ₂ {M = ` x}     = refl
rename-comp ρ₁ ρ₂ {M = M · N} i = rename-comp ρ₁ ρ₂ {M} i · rename-comp ρ₁ ρ₂ {N} i
rename-comp ρ₁ ρ₂ {M = ƛ M}     =
  rename ρ₂ (rename ρ₁ (ƛ M))
    ≡⟨⟩
  ƛ rename (ext ρ₂) (rename (ext ρ₁) M)
    ≡[ i ]⟨ ƛ rename-comp (ext ρ₁) (ext ρ₂) {M} i ⟩
  ƛ rename (ext ρ₂ ∘ ext ρ₁) M
    ≡[ i ]⟨ ƛ rename (funExt (ext-comp ρ₁ ρ₂) i) M ⟩
  ƛ rename (ext (ρ₂ ∘ ρ₁)) M
    ≡⟨⟩
  rename (ρ₂ ∘ ρ₁) (ƛ M) ∎
  where open ≡-Reasoning

----------------------------------------------------------------------
-- punchIn: Weakening at any position

punchIn : ∀ (A : 𝕋) Γ → Rename (Γ ⧺ Δ) (Γ ⧺  A , Δ)
punchIn _ ∅       (Z p) = S Z p
punchIn _ ∅       (S p) = S (S p)
punchIn _ (C , Γ) (Z p) = Z p
punchIn _ (C , Γ) (S p) = S punchIn _ Γ p

punchesIn : ∀ Ξ → Subst Γ Δ → Subst (Ξ ⧺ Γ) (Ξ ⧺ Δ)
punchesIn ∅       σ x     = σ x
punchesIn (C , Ξ) σ (Z p) = ` Z p
punchesIn (C , Ξ) σ (S x) = rename S_ (punchesIn Ξ σ x)

ext-punchIn=punchIn : (x : C ∈ (B , Ξ) ⧺ Γ)
  → ext (punchIn A Ξ) x ≡ punchIn A (B , Ξ) x
ext-punchIn=punchIn {Ξ = ∅}     (Z _) = refl
ext-punchIn=punchIn {Ξ = ∅}     (S _) = refl
ext-punchIn=punchIn {Ξ = C , Ξ} (Z _) = refl
ext-punchIn=punchIn {Ξ = C , Ξ} (S _) = refl

exts-punchesIn=punchesIn
  : (x : A ∈ B , Ξ ⧺ Γ)
  → exts (punchesIn Ξ σ) x ≡ punchesIn (B , Ξ) σ x
exts-punchesIn=punchesIn (Z _) = refl
exts-punchesIn=punchesIn (S _) = refl

S=punchIn : (x : A ∈ Γ) → S x ≡ punchIn B ∅ x
S=punchIn (Z _) = refl
S=punchIn (S x) = refl

punchesIn-punchIn-comm : (σ : Subst Γ Δ)
  → (x : A ∈ Ξ ⧺ Γ)
  → punchesIn Ξ (exts σ) (punchIn B Ξ x) ≡ rename (punchIn B Ξ) (punchesIn Ξ σ x)
punchesIn-punchIn-comm {Ξ = ∅}     σ (Z p) i = rename (funExt S=punchIn i) (σ (Z p))
punchesIn-punchIn-comm {Ξ = ∅}     σ (S p) i = rename (funExt S=punchIn i) (σ (S p))
punchesIn-punchIn-comm {Ξ = T , Ξ} σ (Z p) = refl
punchesIn-punchIn-comm {Ξ = C , Ξ} σ (S p) = begin
  rename S_ (punchesIn Ξ (exts σ) (punchIn _ Ξ p))
    ≡⟨ cong (rename S_) (punchesIn-punchIn-comm σ p) ⟩
  rename S_ (rename (punchIn _ Ξ) (punchesIn Ξ σ p))
    ≡⟨ rename-comp (punchIn _ Ξ) S_ ⟩
  rename (S_ ∘ (punchIn _ Ξ)) (punchesIn Ξ σ p)
    ≡⟨⟩
  rename ((punchIn _ (C , Ξ)) ∘ S_) (punchesIn Ξ σ p)
    ≡⟨ sym (rename-comp S_ (punchIn _ (C , Ξ))) ⟩
  rename (punchIn _ (C , Ξ)) (rename S_ (punchesIn Ξ σ p))
    ∎ where open ≡-Reasoning

punchIn-punchesIn-comm : (σ : Subst Γ Δ)
  → (M : Ξ ⧺ Γ ⊢ A)
  → rename (punchIn B Ξ) M ⟪ punchesIn Ξ (exts σ) ⟫ ≡ rename (punchIn B Ξ) (M ⟪ punchesIn Ξ σ ⟫)
punchIn-punchesIn-comm σ (` x)     = punchesIn-punchIn-comm σ x
punchIn-punchesIn-comm σ (M · N) i = (punchIn-punchesIn-comm σ M i) · (punchIn-punchesIn-comm σ N i)
punchIn-punchesIn-comm {Γ} {Δ} {Ξ} σ (ƛ M) = begin
  rename (punchIn _ Ξ) (ƛ M) ⟪ punchesIn Ξ (exts σ) ⟫
    ≡⟨⟩
  ƛ rename (ext (punchIn _ _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ≡[ i ]⟨ ƛ rename (funExt ext-punchIn=punchIn i) M ⟪ exts (punchesIn _ (exts σ)) ⟫ ⟩
  ƛ rename (punchIn _ (_ , _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ≡⟨ cong ƛ_ (subst-cong exts-punchesIn=punchesIn (rename (punchIn _ (_ , _)) M)) ⟩
  ƛ rename (punchIn _ (_ , _)) M ⟪ punchesIn (_ , _) (exts σ) ⟫
    ≡⟨ cong ƛ_ (punchIn-punchesIn-comm σ M) ⟩
  ƛ rename (punchIn _ (_ , _)) (M ⟪ punchesIn (_ , _) σ ⟫)
    ≡[ i ]⟨ ƛ rename (funExt ext-punchIn=punchIn (~ i)) (M ⟪ punchesIn (_ , _) σ ⟫) ⟩
  ƛ rename (ext (punchIn _ _)) (M ⟪ punchesIn (_ , _) σ ⟫)
    ≡⟨ cong (ƛ_ ∘ rename (ext (punchIn _ _))) (subst-cong (sym ∘ exts-punchesIn=punchesIn) M) ⟩
  ƛ rename (ext (punchIn _ _)) (M ⟪ exts (punchesIn _ σ) ⟫) ∎
  where open ≡-Reasoning

rename-exts : (σ : Subst Γ Δ)
  → (M : Γ ⊢ A)
  → rename (S_ {B = B}) M ⟪ exts σ ⟫ ≡ rename S_ (M ⟪ σ ⟫)
rename-exts σ M = begin
  rename S_ M ⟪ exts σ ⟫
    ≡[ i ]⟨ rename (funExt S=punchIn i) M ⟪ exts σ ⟫ ⟩
  rename (punchIn _ ∅) M ⟪ punchesIn ∅ (exts σ) ⟫
    ≡⟨ punchIn-punchesIn-comm σ M ⟩
  rename (punchIn _ ∅) (M ⟪ σ ⟫)
    ≡[ i ]⟨ rename (funExt S=punchIn (~ i)) (M ⟪ σ ⟫) ⟩
  rename S_ (M ⟪ σ ⟫)
    ∎ where open ≡-Reasoning

ren-ext-comm : (ρ : Rename Γ Δ)
    → (x : A ∈ B , Γ)
    → ren (ext ρ) x ≡ exts (ren ρ) x
ren-ext-comm ρ (Z _) = refl
ren-ext-comm ρ (S _) = refl

----------------------------------------------------------------------
-- Monad Laws

subst-idR : (σ : Subst Γ Δ) {x : A ∈ Γ}
  → ` x ⟪ σ ⟫ ≡ σ x
subst-idR σ = refl

subst-idL
  : (M : Γ ⊢ A)
  → M ⟪ ids ⟫ ≡ M
subst-idL (` x)   = refl
subst-idL (M · N) = cong₂ _·_ (subst-idL M) (subst-idL N)
subst-idL (ƛ_ M)  = begin
  ƛ M ⟪ exts ids ⟫
    ≡[ i ]⟨ ƛ M ⟪ (λ p → exts-ids=ids p i) ⟫ ⟩
  ƛ M ⟪ ids ⟫
    ≡[ i ]⟨ ƛ subst-idL M i ⟩
  ƛ M  ∎
  where
    open ≡-Reasoning
    exts-ids=ids : (x : B ∈ A , Γ) → (exts ids) x ≡ ids x
    exts-ids=ids (Z _) = refl
    exts-ids=ids (S _) = refl

subst-assoc
  : (σ₁ : Subst Γ Δ) (σ₂ : Subst Δ Ξ)
  → (M : Γ ⊢ A)
  →  M ⟪ σ₁ ⟫ ⟪ σ₂ ⟫ ≡ M ⟪ σ₁ ⨟ σ₂ ⟫
subst-assoc σ₁ σ₂ (` x)   = refl
subst-assoc σ₁ σ₂ (M · N) = cong₂ _·_ (subst-assoc σ₁ σ₂ M) (subst-assoc σ₁ σ₂ N)
subst-assoc σ₁ σ₂ (ƛ M)   = begin
  (ƛ M) ⟪ σ₁ ⟫ ⟪ σ₂ ⟫
    ≡⟨⟩
  ƛ M ⟪ exts σ₁ ⟫ ⟪ exts σ₂ ⟫
    ≡[ i ]⟨ ƛ subst-assoc (exts σ₁) (exts σ₂) M i ⟩
  ƛ M ⟪ _⟪ exts σ₂ ⟫ ∘ exts σ₁ ⟫
    ≡[ i ]⟨ ƛ M ⟪ (λ p → exts-subst σ₁ σ₂ p i) ⟫ ⟩
  ƛ M ⟪ exts (σ₁ ⨟ σ₂) ⟫
    ≡⟨⟩
  (ƛ M) ⟪ σ₁ ⨟ σ₂ ⟫ ∎
  where
    open ≡-Reasoning
    exts-subst : (σ₁ : Subst Γ Δ) (σ₂ : Subst Δ Ξ)
      → (x : A ∈ B , Γ)
      → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
    exts-subst σ₁ σ₂ (Z _) = refl
    exts-subst σ₁ σ₂ (S x) = rename-exts σ₂ (σ₁ x)

----------------------------------------------------------------------
--

rename-subst : (ρ : Rename Γ Δ) (σ : Subst Δ Ξ)
  → (M : Γ ⊢ A)
  →  rename ρ M ⟪ σ ⟫ ≡ M ⟪ σ ∘ ρ ⟫
rename-subst ρ σ M = begin
  (rename ρ M) ⟪ σ ⟫
    ≡[ i ]⟨ (rename=subst-ren {ρ = ρ} M i) ⟪ σ ⟫ ⟩
  (M ⟪ ren ρ ⟫) ⟪ σ ⟫
    ≡⟨ subst-assoc (ren ρ) σ M ⟩
  M ⟪ σ ∘ ρ ⟫
    ∎ where open ≡-Reasoning

subst-zero-S=ids : {N : Γ ⊢ B}
  → (x : A ∈ Γ)→ subst-zero N (S x) ≡ ids x
subst-zero-S=ids {Γ} {⋆} (Z {⋆} {⋆} B=A) = refl
subst-zero-S=ids {Γ} {⋆} {⋆} (S x)       = refl

subst-zero-comm : (σ : Subst Γ Δ)
  → (N : Γ ⊢ B) (p : A ∈ B , Γ)
  → (exts σ ⨟ subst-zero (N ⟪ σ ⟫)) p ≡ (subst-zero N ⨟ σ) p
subst-zero-comm {Γ} {Δ} σ N (Z {⋆} {⋆} A=B) = refl
subst-zero-comm {Γ} {Δ} {⋆} {⋆} σ N (S p) = begin
  (rename S_ (σ p)) ⟪ subst-zero (N ⟪ σ ⟫) ⟫
    ≡⟨ cong (_⟪ subst-zero (N ⟪ σ ⟫) ⟫) (rename=subst-ren (σ p)) ⟩
  σ p ⟪ ren S_ ⟫ ⟪ subst-zero (N ⟪ σ ⟫) ⟫
    ≡⟨ subst-assoc (ren S_) (subst-zero (N ⟪ σ ⟫)) (σ p) ⟩
  σ p ⟪ subst-zero (N ⟪ σ ⟫) ∘ S_ ⟫
    ≡[ i ]⟨ σ p ⟪ (λ p → subst-zero-S=ids {N = N ⟪ σ ⟫} p i) ⟫ ⟩
  σ p ⟪ ids ⟫
    ≡⟨ subst-idL (σ p) ⟩
  σ p ∎ where open ≡-Reasoning

------------------------------------------------------------------------------
-- Substitution Lemma

subst-ssubst : (σ : Subst Γ Δ)
  → (M : A , Γ ⊢ B) (N : Γ ⊢ A)
  → M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ] ≡ M [ N ] ⟪ σ ⟫
subst-ssubst σ M N = begin
  M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ]
    ≡⟨ subst-assoc (exts σ) (subst-zero (N ⟪ σ ⟫)) M ⟩
  M ⟪ exts σ ⨟ subst-zero (N ⟪ σ ⟫) ⟫
    ≡[ i ]⟨ M ⟪ (λ p → subst-zero-comm σ N p i) ⟫ ⟩
  M ⟪ subst-zero N ⨟ σ ⟫
    ≡⟨ sym (subst-assoc (subst-zero N) σ M) ⟩
  (M ⟪ subst-zero N ⟫) ⟪ σ ⟫
    ∎ where open ≡-Reasoning

rename-ssubst : (ρ : Rename Γ Δ)
  → (M : A , Γ ⊢ B) (N : Γ ⊢ A)
  → rename (ext ρ) M [ rename ρ N ] ≡ rename ρ (M [ N ])
rename-ssubst {Γ} {Δ} {A} {B} ρ M N = begin
  rename (ext ρ) M [ rename ρ N ]
    ≡⟨ cong (_⟪ subst-zero (rename ρ N) ⟫) (rename=subst-ren M) ⟩
  M ⟪ ren (ext ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ≡⟨ cong _⟪ subst-zero (rename ρ N) ⟫ (subst-cong (ren-ext-comm ρ) M) ⟩
  M ⟪ exts (ren ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ≡⟨ subst-cong (λ { (Z {⋆} {⋆} B=A) → rename=subst-ren N; (S_ {⋆} {_} {⋆} x) → refl}) (M ⟪ exts (ren ρ) ⟫) ⟩
  M ⟪ exts (ren ρ) ⟫ [ N ⟪ ren ρ ⟫ ]
    ≡⟨ subst-ssubst (ren ρ) M N ⟩
  M [ N ] ⟪ ren ρ ⟫
    ≡⟨ sym (rename=subst-ren _) ⟩
  rename ρ (M [ N ]) ∎ where open ≡-Reasoning

subst-rename-∅ : {ρ : Rename ∅ Γ} (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → rename ρ M ⟪ σ ⟫ ≡ M
subst-rename-∅ {ρ = ρ} σ M = begin
  rename ρ M ⟪ σ ⟫
    ≡⟨ rename-subst ρ σ M ⟩
  M ⟪ σ ∘ ρ ⟫
    ≡[ i ]⟨ M ⟪ funExt {f = σ ∘ ρ} {g = ids} (λ ()) i ⟫ ⟩
  M ⟪ ids ⟫
    ≡⟨ subst-idL M ⟩
  M ∎ where open ≡-Reasoning

------------------------------------------------------------------------------
-- Substitution respects reduction

module _ where
  open -↠-Reasoning

  rename-reduce : {ρ : Rename Γ Δ} {M N : Γ ⊢ A}
    → M -→ N
    → rename ρ M -→ rename ρ N
  rename-reduce {ρ = ρ} (β {M = M} {N}) =
    subst (rename ρ ((ƛ M) · N) -→_) (rename-ssubst ρ M N) β
  rename-reduce (ζ M-→N)  = ζ  (rename-reduce M-→N)
  rename-reduce (ξₗ M-→N) = ξₗ (rename-reduce M-→N)
  rename-reduce (ξᵣ M-→N) = ξᵣ (rename-reduce M-→N)

  rename-reduce* : {ρ : Rename Γ Δ} {M N : Γ ⊢ A}
    → M -↠ N
    → rename ρ M -↠ rename ρ N
  rename-reduce* (M ∎)               = -↠-refl
  rename-reduce* (L -→⟨ L-→M ⟩ M-↠N) = _ -→⟨ rename-reduce L-→M ⟩ rename-reduce* M-↠N

  subst-reduce : {σ : Subst Γ Δ} {M N : Γ ⊢ A}
    → M -→ N
    → M ⟪ σ ⟫ -→ N ⟪ σ ⟫
  subst-reduce {σ = σ} (β {M = M} {N}) =
    subst ((ƛ M) ⟪ σ ⟫ · N ⟪ σ ⟫ -→_) (subst-ssubst σ M N) β
  subst-reduce (ζ M-→N)  = ζ  (subst-reduce M-→N)
  subst-reduce (ξₗ M-→N) = ξₗ (subst-reduce M-→N)
  subst-reduce (ξᵣ M-→N) = ξᵣ (subst-reduce M-→N)

  subst-reduce* : {σ : Subst Γ Δ} {M N : Γ ⊢ A}
    → M -↠ N
    → M ⟪ σ ⟫ -↠ N ⟪ σ ⟫
  subst-reduce* (M ∎)               = -↠-refl
  subst-reduce* (L -→⟨ L-→M ⟩ M-↠N) = _ -→⟨ subst-reduce L-→M ⟩ subst-reduce* M-↠N

------------------------------------------------------------------------------
-- Special cut rule
-- TODO: Simplify these special cases

γ : (N : A , ∅ ⊢ B) → Subst (B , ∅) (A , ∅)
γ {⋆} {⋆} N {⋆} (Z B=A) = N

_∘′_ : {A B C : 𝕋}
  → B , ∅ ⊢ C
  → A , ∅ ⊢ B
  → A , ∅ ⊢ C
_∘′_ {A} {B} {C} M N = M ⟪ γ N ⟫

∘-ssubst-ssubst : (L : B , ∅ ⊢ C) (M : A , ∅ ⊢ B) (N : ∅ ⊢ A)
  → (L ∘′ M) [ N ] ≡ L [ M [ N ] ]
∘-ssubst-ssubst {⋆} {⋆} {⋆} L M N = begin
  (L ∘′ M) [ N ]
    ≡⟨⟩
  L ⟪ γ M ⟫ ⟪ subst-zero N ⟫
    ≡⟨ subst-assoc (γ M) (subst-zero N) L ⟩
  L ⟪ γ M ⨟ subst-zero N ⟫
    ≡⟨ subst-cong (λ { (Z {⋆} {⋆} B=A) → refl}) L ⟩
  L [ M [ N ] ] ∎
  where open ≡-Reasoning

∘′-id-left  : (M : A , ∅ ⊢ B) → (` Z refl) ∘′ M ≡ M
∘′-id-left {⋆} {⋆} M = refl

∘′-id-right : (M : A , ∅ ⊢ B) → M ∘′ (` Z refl) ≡ M
∘′-id-right {⋆} {⋆} M = begin
  M ⟪ γ (` Z refl) ⟫
    ≡⟨ subst-cong γZ=ids M ⟩
  M ⟪ ids ⟫
    ≡⟨ subst-idL M ⟩
  M ∎
  where
    open ≡-Reasoning
    γZ=ids : {A : 𝕋} (x : A ∈ B , ∅) → γ (` Z refl) x ≡ ids  x
    γZ=ids {⋆} {⋆} (Z B=A) i = ` Z (≟→isSet ⋆ ⋆ refl B=A i)

∘′-assoc    :  (L : C , ∅ ⊢ B) (M : B , ∅ ⊢ C) (N : A , ∅ ⊢ B)
  → (L ∘′ M) ∘′ N ≡ L ∘′ (M ∘′ N)
∘′-assoc {⋆} {⋆} {⋆} L M N = begin
  L ⟪ γ M ⟫ ⟪ γ N ⟫
    ≡⟨ subst-assoc _ _ L ⟩
  L ⟪ γ M ⨟ γ N ⟫
    ≡⟨ subst-cong (λ { {⋆} → γ-subst-dist {M = M} }) L ⟩
  L ⟪ γ (M ⟪ γ N ⟫) ⟫ ∎
  where
    open ≡-Reasoning
    γ-subst-dist : {A B C : 𝕋} {M : B , ∅ ⊢ C} {N : A , ∅ ⊢ B}
      → (x : A ∈ C , ∅) → γ M x ⟪ γ N ⟫ ≡ γ (M ⟪ γ N ⟫) x
    γ-subst-dist {⋆} {⋆} {⋆} (Z B=A) = refl
