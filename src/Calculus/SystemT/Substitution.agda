{-# OPTIONS --without-K --cubical #-}

-- System T

module Calculus.SystemT.Substitution where

open import Prelude
  hiding (_,_; ⟨_⟩; ⟪_⟫)

open import Calculus.Type           public
open import Calculus.Context        public
open import Calculus.SystemT.Base   public

------------------------------------------------------------------------------
-- Properties of subst, rename

private
  variable
    Γ Δ : Cxt
    A B : 𝕋

--postulate
--  rename-cong : {ρ ρ′ : Rename Γ Δ} → (∀ {A} → ρ {A} ≗ ρ′ {A}) → (M : Γ ⊢ A) → rename ρ M ≡ rename ρ′ M
--  subst-` : (M : ∅ ⊢ A) → M ⟪ `_ ⟫ ≡ M
--  subst-cong : {σ σ′ : Subst Γ Δ} → (∀ {A} → σ {A} ≗ σ′ {A}) → (M : Γ ⊢ A) → M ⟪ σ ⟫ ≡ M ⟪ σ′ ⟫
--  subst-rename : (ρ : Rename Γ Δ) (σ : Subst Δ Δ′) (M : Γ ⊢ A) → rename ρ M ⟪ σ ⟫ ≡ M ⟪ σ ∘ ρ ⟫
--  subst-subst : (σ : Subst Γ Δ) (σ′ : Subst Δ Δ′) (M : Γ ⊢ A) → M ⟪ σ ⟫ ⟪ σ′ ⟫ ≡ M ⟪ _⟪ σ′ ⟫ ∘ σ ⟫

postulate
  subst-rename-∅ : (ρ : Rename ∅ Γ) (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → rename ρ M ⟪ σ ⟫ ≡ M
--subst-rename-∅ ρ σ M =  
--    rename ρ M ⟪ σ ⟫
--  ≡⟨ {!!} ⟩ -- subst-rename ρ σ M
--    M ⟪ σ ∘ ρ ⟫
--  ≡⟨ {!!} ⟩ -- subst-cong (λ ()) M
--    M ⟪ `_ ⟫
--  ≡⟨ {!!} ⟩ -- subst-` M
--    M
--  ∎

subst-↑ : (σ : Subst Γ ∅) → (M : ∅ ⊢ A) → ↑ M ⟪ σ ⟫ ≡ M
subst-↑ = subst-rename-∅ λ ()
