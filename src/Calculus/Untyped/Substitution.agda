{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Substitution where

open import Prelude
open import Calculus.Context
open import Calculus.Untyped.Base


private
  variable
    A B C   : 𝕋
    ρ ρ₁ ρ₂ : Rename Γ Δ
    σ σ₁ σ₂ : Subst Γ Δ

infixr 5 _⨟_

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
(σ ⨟ τ) x = σ x ⟪ τ ⟫ 

ids : Subst Γ Γ
ids = `_

----------------------------------------------------------------------
-- Congruence rules
rename-cong 
  : (∀ {A} (x : A ∈ Γ) → ρ₁ x ≡ ρ₂ x)
  → (M : Γ ⊢ A)
  → rename ρ₁ M ≡ rename ρ₂ M
rename-cong p (` x)   i = ` p x i
rename-cong p (M · N) i = rename-cong p M i · rename-cong p N i
rename-cong {ρ₁ = ρ₁} {ρ₂} p (ƛ M) i = ƛ rename-cong rho M i
  where
    rho : (x : A ∈ B , _) → ext ρ₁ x ≡ ext ρ₂ x
    rho (Z _)   = refl
    rho (S x) i = S p x i

subst-cong
  : ({A : 𝕋} (x : A ∈ Γ) → σ₁ x ≡ σ₂ x)
  → (M : Γ ⊢ A)
  → M ⟪ σ₁ ⟫ ≡ M ⟪ σ₂ ⟫
subst-cong p (` x)    = p x
subst-cong p (M · N)  = cong₂ _·_ (subst-cong p M) (subst-cong p N)

subst-cong p (ƛ M)    = cong ƛ_ (subst-cong 
  (λ {(Z _) → refl ; (S x) → cong (rename S_) (p x)}) M)

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
    ≡⟨ cong ƛ_ (subst-cong (ren-ext ρ) M) ⟩
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
rename-comp ρ₁ ρ₂ {M = ` x}   = refl
rename-comp ρ₁ ρ₂ {M = M · N} i = rename-comp ρ₁ ρ₂ {M} i · rename-comp ρ₁ ρ₂ {N} i 
rename-comp ρ₁ ρ₂ {M = ƛ M}   =
  rename ρ₂ (rename ρ₁ (ƛ M))
    ≡⟨⟩
  ƛ rename (ext ρ₂) (rename (ext ρ₁) M)
    ≡[ i ]⟨ ƛ rename-comp (ext ρ₁) (ext ρ₂) {M} i ⟩
  ƛ rename (ext ρ₂ ∘ ext ρ₁) M
    ≡[ i ]⟨ ƛ rename-cong (ext-comp ρ₁ ρ₂) M i ⟩
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
punchesIn-punchIn-comm {Ξ = ∅}     σ (Z p) = rename-cong S=punchIn (σ (Z p))
punchesIn-punchIn-comm {Ξ = ∅}     σ (S p) = rename-cong S=punchIn (σ (S p))
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
    ∎
  where open ≡-Reasoning

punchIn-punchesIn-comm : (σ : Subst Γ Δ)
  → (M : Ξ ⧺ Γ ⊢ A)
  → rename (punchIn B Ξ) M ⟪ punchesIn Ξ (exts σ) ⟫ ≡ rename (punchIn B Ξ) (M ⟪ punchesIn Ξ σ ⟫)
punchIn-punchesIn-comm σ (` x)     = punchesIn-punchIn-comm σ x
punchIn-punchesIn-comm σ (M · N) i = (punchIn-punchesIn-comm σ M i) · (punchIn-punchesIn-comm σ N i)
punchIn-punchesIn-comm {Γ} {Δ} {Ξ} σ (ƛ M) = begin
  rename (punchIn _ Ξ) (ƛ M) ⟪ punchesIn Ξ (exts σ) ⟫
    ≡⟨⟩
  ƛ rename (ext (punchIn _ _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ≡⟨ cong (ƛ_ ∘ _⟪ exts (punchesIn _ (exts σ)) ⟫) (rename-cong ext-punchIn=punchIn M) ⟩
  ƛ rename (punchIn _ (_ , _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ≡⟨ cong ƛ_ (subst-cong exts-punchesIn=punchesIn (rename (punchIn _ (_ , _)) M)) ⟩
  ƛ rename (punchIn _ (_ , _)) M ⟪ punchesIn (_ , _) (exts σ) ⟫
    ≡⟨ cong ƛ_ (punchIn-punchesIn-comm σ M) ⟩
  ƛ rename (punchIn _ (_ , _)) (M ⟪ punchesIn (_ , _) σ ⟫)
    ≡⟨ cong ƛ_ (rename-cong (sym ∘ ext-punchIn=punchIn) (M ⟪ punchesIn (_ , _) σ ⟫)) ⟩
  ƛ rename (ext (punchIn _ _)) (M ⟪ punchesIn (_ , _) σ ⟫)
    ≡⟨ cong (ƛ_ ∘ rename (ext (punchIn _ _))) (subst-cong (sym ∘ exts-punchesIn=punchesIn) M) ⟩
  ƛ rename (ext (punchIn _ _)) (M ⟪ exts (punchesIn _ σ) ⟫) ∎
  where
    open ≡-Reasoning

rename-exts : (σ : Subst Γ Δ)
  → (M : Γ ⊢ A)
  → rename (S_ {B = B}) M ⟪ exts σ ⟫ ≡ rename S_ (M ⟪ σ ⟫)
rename-exts σ M = begin
  rename S_ M ⟪ exts σ ⟫
    ≡⟨ cong _⟪ exts σ ⟫ (rename-cong S=punchIn M) ⟩
  rename (punchIn _ ∅) M ⟪ punchesIn ∅ (exts σ) ⟫
    ≡⟨ punchIn-punchesIn-comm σ M ⟩
  rename (punchIn _ ∅) (M ⟪ σ ⟫)
    ≡⟨ rename-cong (sym ∘ S=punchIn) (M ⟪ σ ⟫) ⟩
  rename S_ (M ⟪ σ ⟫)
    ∎ 
  where
    open ≡-Reasoning

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
subst-idL (` x)      = refl
subst-idL (M · N)    = cong₂ _·_    (subst-idL M) (subst-idL N)
subst-idL (ƛ_ M)     = begin
  ƛ M ⟪ exts ids ⟫ 
    ≡⟨ cong ƛ_ (subst-cong exts-ids=ids M) ⟩ 
  ƛ M ⟪ ids ⟫
    ≡⟨ cong ƛ_ (subst-idL M) ⟩
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
subst-assoc σ₁ σ₂ (` x)      = refl
subst-assoc σ₁ σ₂ (M · N)    = cong₂ _·_ (subst-assoc σ₁ σ₂ M) (subst-assoc σ₁ σ₂ N)
subst-assoc σ₁ σ₂ (ƛ M)      = begin
  (ƛ M) ⟪ σ₁ ⟫ ⟪ σ₂ ⟫
    ≡⟨⟩
  ƛ M ⟪ exts σ₁ ⟫ ⟪ exts σ₂ ⟫
    ≡⟨ cong ƛ_ (subst-assoc (exts σ₁) (exts σ₂) M) ⟩
  ƛ M ⟪ _⟪ exts σ₂ ⟫ ∘ exts σ₁ ⟫
    ≡⟨ cong ƛ_ (subst-cong (exts-subst σ₁ σ₂) M) ⟩
  ƛ M ⟪ exts (σ₁ ⨟ σ₂) ⟫
    ≡⟨⟩
  (ƛ M) ⟪ σ₁ ⨟ σ₂ ⟫ ∎
  where
    open ≡-Reasoning
    exts-subst : (σ₁ : Subst Γ Δ) (σ₂ : Subst Δ Ξ)
      → (x : A ∈ B , Γ) 
      → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
    exts-subst σ₁ σ₂ (Z _) = refl
    exts-subst σ₁ σ₂ (S x) = begin
      (exts σ₁ ⨟ exts σ₂) (S x)
        ≡⟨⟩
      rename S_ (σ₁ x) ⟪ exts σ₂ ⟫ 
        ≡⟨ rename-exts σ₂ (σ₁ x)  ⟩
      rename S_ (σ₁ x ⟪ σ₂ ⟫)
        ≡⟨⟩
      exts (σ₁ ⨟ σ₂) (S x)
        ∎

----------------------------------------------------------------------
-- 

rename-subst : (ρ : Rename Γ Δ) (σ : Subst Δ Ξ)
  → (M : Γ ⊢ A)
  →  rename ρ M ⟪ σ ⟫ ≡ M ⟪ σ ∘ ρ ⟫
rename-subst ρ σ M = begin
  (rename ρ M) ⟪ σ ⟫ 
    ≡⟨ cong _⟪ σ ⟫ (rename=subst-ren M) ⟩
  (M ⟪ ren ρ ⟫) ⟪ σ ⟫ 
    ≡⟨ subst-assoc (ren ρ) σ M ⟩
  M ⟪ ren ρ ⨟ σ ⟫
    ≡⟨⟩
  M ⟪ σ ∘ ρ ⟫
    ∎
  where open ≡-Reasoning

subst-zero-comm : (σ : Subst Γ Δ)
  → (N : Γ ⊢ B) (p : A ∈ B , Γ)
  → (exts σ ⨟ subst-zero (N ⟪ σ ⟫)) p ≡ (subst-zero N ⨟ σ) p
subst-zero-comm         σ N (Z A=B) = {!!}
subst-zero-comm {Γ} {Δ} σ N (S p) = begin
  (rename S_ (σ p)) ⟪ subst-zero (N ⟪ σ ⟫) ⟫ 
    ≡⟨ cong (_⟪ subst-zero (N ⟪ σ ⟫) ⟫) (rename=subst-ren (σ p)) ⟩
  σ p ⟪ ren S_ ⟫ ⟪ subst-zero (N ⟪ σ ⟫) ⟫ 
    ≡⟨ subst-assoc (ren S_) (subst-zero (N ⟪ σ ⟫)) (σ p) ⟩
  σ p ⟪ subst-zero (N ⟪ σ ⟫) ∘ S_ ⟫ 
    ≡⟨ refl ⟩
  σ p ⟪ ids ⟫ 
    ≡⟨ subst-idL (σ p) ⟩
  σ p ∎
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Substitution Lemma

  
subst-ssubst : (σ : Subst Γ Δ)
  → (M : A , Γ ⊢ B) (N : Γ ⊢ A)
  → M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ] ≡ M [ N ] ⟪ σ ⟫ 
subst-ssubst σ M N = begin
  M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ]
    ≡⟨ subst-assoc (exts σ) (subst-zero (N ⟪ σ ⟫)) M ⟩
  M ⟪ exts σ ⨟ subst-zero (N ⟪ σ ⟫) ⟫
    ≡⟨ subst-cong (subst-zero-comm σ N) M ⟩ 
  M ⟪ subst-zero N ⨟ σ ⟫
    ≡⟨ sym (subst-assoc (subst-zero N) σ M) ⟩
  (M ⟪ subst-zero N ⟫) ⟪ σ ⟫ 
    ∎
  where open ≡-Reasoning

rename-ssubst : (ρ : Rename Γ Δ)
  → (M : A , Γ ⊢ B) (N : Γ ⊢ A)
  → rename (ext ρ) M [ rename ρ N ] ≡ rename ρ (M [ N ])
rename-ssubst ρ M N = begin
  rename (ext ρ) M [ rename ρ N ]
    ≡⟨ cong (_⟪ subst-zero (rename ρ N) ⟫) (rename=subst-ren M) ⟩
  M ⟪ ren (ext ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ≡⟨ cong _⟪ subst-zero (rename ρ N) ⟫ (subst-cong (ren-ext-comm ρ) M) ⟩
  M ⟪ exts (ren ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ≡⟨ subst-cong (λ { (Z p) → {!!} ; (S x) → refl}) (M ⟪ exts (ren ρ) ⟫) ⟩
  M ⟪ exts (ren ρ) ⟫ [ N ⟪ ren ρ ⟫ ]
    ≡⟨ subst-ssubst (ren ρ) M N ⟩
  M [ N ] ⟪ ren ρ ⟫
    ≡⟨ sym (rename=subst-ren _) ⟩
  rename ρ (M [ N ])
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------------
-- Substitution respects reduction

rename-reduce : {ρ : Rename Γ Δ} {M N : Γ ⊢ A}
  → M -→ N
  → rename ρ M -→ rename ρ N
rename-reduce {ρ = ρ} (β {M = M} {N}) =
  subst (rename ρ ((ƛ M) · N) -→_) (rename-ssubst ρ M N) β
  where open -↠-Reasoning
rename-reduce (ζ M-→N)  = ζ  (rename-reduce M-→N)
rename-reduce (ξₗ M-→N) = ξₗ (rename-reduce M-→N)
rename-reduce (ξᵣ M-→N) = ξᵣ (rename-reduce M-→N)

subst-reduce : {σ : Subst Γ Δ} {M N : Γ ⊢ A}
  → M -→ N
  → M ⟪ σ ⟫ -→ N ⟪ σ ⟫
subst-reduce {σ = σ} (β {M = M} {N}) =
  subst ((ƛ M) ⟪ σ ⟫ · N ⟪ σ ⟫ -→_) (subst-ssubst σ M N) β
  where open -↠-Reasoning
subst-reduce (ζ M-→N)  = ζ  (subst-reduce M-→N)
subst-reduce (ξₗ M-→N) = ξₗ (subst-reduce M-→N)
subst-reduce (ξᵣ M-→N) = ξᵣ (subst-reduce M-→N)

subst-rename-∅ : (ρ : Rename ∅ Γ) (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → rename ρ M ⟪ σ ⟫ ≡ M
subst-rename-∅ ρ σ M = begin
  rename ρ M ⟪ σ ⟫
    ≡⟨ rename-subst ρ σ M ⟩
  M ⟪ σ ∘ ρ ⟫
    ≡⟨ subst-cong (λ ()) M ⟩
  M ⟪ ids ⟫
    ≡⟨ subst-idL M ⟩ 
  M ∎
  where open ≡-Reasoning

subst-↑ : (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → ↑ M ⟪ σ ⟫ ≡ M 
subst-↑ = subst-rename-∅ λ ()