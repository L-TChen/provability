{-# OPTIONS --without-K --cubical #-}

open import Prelude
open import Algebra.PCA.Base

module Algebra.PCA.Combinator (𝓐 : OPCA 𝓥 𝓤) where
open OpcaStr (str 𝓐)
  renaming (⟦_⟧_ to ⟦_⟧ᵗ_)
open Term-Reasoning 𝓐

𝐼ᵗ : Term 0
𝐼ᵗ = ƛ ` 0
𝐾ᵗ : Term 0
𝐾ᵗ = ƛ ƛ ` 1

𝑆ᵗ : Term 0
-- S = λ x. λ y. λ z. xz(yz)
𝑆ᵗ = ƛ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)

𝐼a≼a : ∀ a → ⟦ 𝐼ᵗ ⊙ ᵒ a ⟧₀ ℒ≼ ⟦ ᵒ a ⟧₀
𝐼a≼a a = completeness

𝐾ab≼a : ∀ a b
  → ⟦ (ƛ ƛ ` 1) ⊙ ᵒ a ⊙ ᵒ b ⟧₀ ℒ≼ ⟦ ᵒ a ⟧₀
𝐾ab≼a a b = begin
  ⟦ (ƛ ƛ ` 1) ⊙ ᵒ a ⊙ ᵒ b ⟧ []
    ≼⟨ •ₗ-respect-ℒ≼ (⟦ (ƛ ƛ ` 1) ⊙ ᵒ a ⟧₀) (⟦ ƛ ` 1 ⟧ᵗ (a ∷ [])) (pure b) completeness ⟩
  ⟦ (ƛ ` 1) ⊙ ᵒ b ⟧ a ∷ []
    ≼⟨ completeness  ⟩
  ⟦ ` 1 ⟧ b ∷ a ∷ []
    ∎ 

𝐾↓ : ⟦ 𝐾ᵗ ⟧₀ ↓ 
𝐾↓ = truncElim (λ _ → ⟦ 𝐾ᵗ ⟧₀ ↓isProp) (λ a → 𝐾ab≼a a a _ .fst .fst .fst) nonEmpty

𝑆abc≼acbc : ∀ a b c → ⟦ 𝑆ᵗ ⊙ ᵒ a ⊙ ᵒ b ⊙ ᵒ c ⟧₀ ℒ≼ ⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀
𝑆abc≼acbc a b c = begin
  ⟦ 𝑆ᵗ ⊙ ᵒ a ⊙ ᵒ b ⊙ ᵒ c ⟧ []
    ≼⟨ •ₗ-respect-ℒ≼ ⟦ 𝑆ᵗ ⊙ ᵒ a ⊙ ᵒ b ⟧₀ (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b ⟧ᵗ _)  (pure c)
       (•ₗ-respect-ℒ≼ ⟦ 𝑆ᵗ ⊙ ᵒ a ⟧₀ (⟦ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ᵗ _) (pure b) completeness)
     ⟩
  ⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b  ⊙ ᵒ c ⟧ a ∷ []
    ≼⟨ •ₗ-respect-ℒ≼ (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b ⟧ᵗ _) (⟦ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ᵗ _) (pure c) completeness
     ⟩
  ⟦ (ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ c ⟧ b ∷ a ∷ []
    ≼⟨ completeness ⟩
  ⟦ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ c ∷ b ∷ a ∷ []
    ∎
