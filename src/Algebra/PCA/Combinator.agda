{-# OPTIONS --without-K --cubical #-}

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc)

open import Prelude
open import Algebra.PCA.Base

module Algebra.PCA.Combinator (𝓐 : OPCA 𝓥 𝓤) where
open OpcaStr (str 𝓐)

open import Relation.Binary.Preorder

𝐼ᵗ : Term 0
𝐼ᵗ = ƛ ` 0
𝐾ᵗ : Term 0
𝐾ᵗ = ƛ ƛ ` 1

𝑆ᵗ : Term 0
-- S = λ x. λ y. λ z. xz(yz)
𝑆ᵗ = (ƛ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0))

𝐼a≼a : ∀ a → ⟦ 𝐼ᵗ ⊙ ᵒ a ⟧₀ ≼ᵖ ⟦ ᵒ a ⟧₀
𝐼a≼a a = completeness (` 0) a []

𝐾ab≼a : ∀ a b
  → ⟦ 𝐾ᵗ ⊙ ᵒ a ⊙ ᵒ b ⟧₀  ≼ᵖ ⟦ ᵒ a ⟧₀
𝐾ab≼a a b = ≼ᵖ-isTransitive ⟦ 𝐾ᵗ ⊙ ᵒ a ⊙ ᵒ b ⟧₀ (⟦ (ƛ ` 1) ⊙ ᵒ b ⟧₁ a) ⟦ ᵒ a ⟧₀ Kab≼λxab λxab≼a
  where
    Kab≼λxab : ⟦ (ƛ ƛ ` 1) ⊙ ᵒ a ⊙ ᵒ b ⟧₀ ≼ᵖ ⟦ (ƛ ` 1) ⊙ ᵒ b ⟧₁ a
    Kab≼λxab = •-respect-≼ᵖ
      (⟦ ƛ ƛ ` 1 ⟧ [] • pure a) (pure b) (⟦ ƛ ` 1 ⟧ (a ∷ [])) (pure b)
      (completeness (ƛ ` 1) a []) λ _ → _ , (≼-isReflexive b)

    λxab≼a : ⟦ (ƛ ` 1) ⊙ ᵒ b ⟧₁ a ≼ᵖ ⟦ ᵒ a ⟧ (b ∷ a ∷ [])
    λxab≼a = completeness (` 1) b (a ∷ [])

𝐾↓ : ⟦ 𝐾ᵗ ⟧₀ ↓ 
𝐾↓ = truncElim (λ _ → ⟦ 𝐾ᵗ ⟧₀ ↓isProp) (λ a → 𝐾ab≼a a a _ .fst .fst .fst) nonEmpty

-- TODO: Simplify the following & Fix _≼⟨_⟩_
Sabc≼acbc : ∀ a b c → ⟦ 𝑆ᵗ ⊙ ᵒ a ⊙ ᵒ b ⊙ ᵒ c ⟧₀ ≼ᵖ ⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀
Sabc≼acbc a b c =
  _≼⟨_⟩_ {⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b  ⊙ ᵒ c ⟧₁ a} {⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀} ⟦ 𝑆ᵗ ⊙ ᵒ a ⊙ ᵒ b ⊙ ᵒ c ⟧₀
  --
    (•-respect-≼ᵖ
      ⟦ 𝑆ᵗ ⊙ ᵒ a ⊙ ᵒ b ⟧₀ (pure c)
      (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b ⟧₁ a)  (pure c)
      (•-respect-≼ᵖ
        ⟦ 𝑆ᵗ ⊙ ᵒ a ⟧₀ (pure b)
        (⟦ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧₁ a) (pure b)
          (completeness (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) _ _) (≼ᵖ-isReflexive (pure b))) (≼ᵖ-isReflexive (pure c)))
  --
  (_≼⟨_⟩_ {⟦ (ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ c ⟧ (b ∷ a ∷ [])} {⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀} (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b  ⊙ ᵒ c ⟧₁ a)
    (•-respect-≼ᵖ
      (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ b ⟧₁ a) (pure c)
      (⟦ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ (b ∷ a ∷ [])) (pure c)
        (completeness (ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) _ _) (≼ᵖ-isReflexive (pure c)))
  (_≼⟨_⟩_ {⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀} {⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀} (⟦ (ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᵒ c ⟧ (b ∷ a ∷ []))
    (completeness (` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) _ _)
  (⟦ ᵒ a ⊙ ᵒ c ⊙ (ᵒ b ⊙ ᵒ c) ⟧₀ ∎≼)))
  where
    open ≼-Reasoning ≼ᵖ-isPreorder
