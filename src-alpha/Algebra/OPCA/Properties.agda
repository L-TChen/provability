{-# OPTIONS --without-K --cubical #-}
module Algebra.OPCA.Properties where

open import Prelude
  hiding (_≡⟨_⟩_)
open import Algebra.OPCA.Base
import      Algebra.OPAS.Properties as OPASₚ

module _ (𝔄 : OPCA 𝓥 𝓤) where
  open OpcaStr (str 𝔄) renaming (⟦_⟧_ to ⟦_⟧_)
  private
    A = ⟨ 𝔄 ⟩

  isTrivial : 𝓤 ⊔ 𝓥 ̇
  isTrivial = ∃[ bot ꞉ A ] Π[ a ꞉ A ] (bot ≼ a)

  isPseudoTrivial : 𝓤 ⊔ 𝓥 ̇
  isPseudoTrivial = (a b : A) → ∃[ c ꞉ A ] c ≼ a × c ≼ b

  Trivial⇒PseudoTrivial : isTrivial → isPseudoTrivial
  Trivial⇒PseudoTrivial = truncElim (λ _ → isPropΠ λ _ → isPropΠ (λ _ → propTruncIsProp))
    λ { (c , c≼a) a b → ∣ c , (c≼a a) , (c≼a b) ∣}
  

module Combinators (𝔄 : OPCA 𝓥 𝓤) where
  open OpcaStr (str 𝔄) renaming (⟦_⟧_ to ⟦_⟧ᵗ_)
  open OPASₚ.Structure (OPCA→OPAS 𝔄)

  private
    A = ⟨ 𝔄 ⟩
    variable
      n m : ℕ

  𝐼 𝐾 𝐾₂ 𝑃 𝑆 : Term A n
  -- I = λ x. x
  𝐼 = ƛ ` 0
  -- K = λ x. λy. x
  𝐾 = ƛ ƛ ` 1
  𝐾₂ = ƛ ƛ ` 0
  -- 𝑃 = λ x y z. z x y
  𝑃 = ƛ ƛ ƛ ` 2 ⊙ ` 0 ⊙ ` 1
  -- S = λ x. λ y. λ z. xz(yz)
  𝑆 = ƛ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)

  abstract 
    𝐼a≼a : (a : A) → ⟦ 𝐼 ⊙ ᶜ a ⟧₀ ℒ≼ ⟦ ` 0  ⟧ᵗ [ a ]
    𝐼a≼a a = completeness

    𝐾ab≼a : ∀ a b
      → ⟦ 𝐾 ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
    𝐾ab≼a a b = begin
      ⟦ 𝐾 ⊙ ᶜ a ⊙ ᶜ b ⟧ []
        ≼⟨ •ₗ-respect-ℒ≼ ⟦ 𝐾 ⊙ ᶜ a ⟧₀ (⟦ ƛ ` 1 ⟧ᵗ [ a ]) (pure b) completeness ⟩
      ⟦ (ƛ ` 1) ⊙ ᶜ b ⟧ [ a ]
        ≼⟨ completeness ⟩
      ⟦ ` 1 ⟧ b ∷ [ a ]
        ∎ 
      where open ≼-Reasoning (OPCA→OPAS 𝔄)

    𝑆abc≼acbc : ∀ a b c → ⟦ 𝑆 ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧₀ ℒ≼ ⟦ ᶜ a ⊙ ᶜ c ⊙ (ᶜ b ⊙ ᶜ c) ⟧₀
    𝑆abc≼acbc a b c = begin
      ⟦ 𝑆 ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧ []
        ≼⟨ •ₗ-respect-ℒ≼ ⟦ 𝑆 ⊙ ᶜ a ⊙ ᶜ b ⟧₀ (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᶜ b ⟧ᵗ _)  (pure c)
          (•ₗ-respect-ℒ≼ ⟦ (ƛ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᶜ a ⟧₀ (⟦ ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ᵗ _) (pure b) completeness) ⟩
      ⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᶜ b  ⊙ ᶜ c ⟧ [ a ]
        ≼⟨ •ₗ-respect-ℒ≼ (⟦ (ƛ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᶜ b ⟧ᵗ _) (⟦ ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ᵗ _) (pure c) completeness ⟩
      ⟦ (ƛ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)) ⊙ ᶜ c ⟧ b ∷ [ a ]
        ≼⟨ completeness ⟩
      ⟦ ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0) ⟧ c ∷ b ∷ [ a ]
        ∎
      where open ≼-Reasoning (OPCA→OPAS 𝔄)

    𝐼a↓ : (a : A) → ⟦ 𝐼 ⊙ ᶜ a ⟧₀ ↓
    𝐼a↓ a = 𝐼a≼a a tt* .fst

    𝐼↓ : ⟦ 𝐼 ⟧₀ ↓
    𝐼↓ = truncElim (λ _ → ⟦ 𝐼 ⟧₀ ↓-isProp) (fst ∘ 𝐼a↓) nonEmpty 

    𝐾ab↓ : (a b : A) → ⟦ 𝐾 ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ↓
    𝐾ab↓ a b = 𝐾ab≼a a b _ .fst

    𝐾a↓ : (a : A) → ⟦ 𝐾 ⊙ ᶜ a ⟧₀ ↓
    𝐾a↓ a = 𝐾ab↓ a a .fst

    𝐾↓ : ⟦ 𝐾 ⟧₀ ↓
    𝐾↓ = truncElim (λ _ → ⟦ 𝐾 ⟧₀ ↓-isProp) (fst ∘ 𝐾a↓) nonEmpty

    𝑖¹ : A → A
    𝑖¹ a = value ⟦ 𝐼 ⊙ ᶜ a ⟧₀ (𝐼a↓ _)

  𝑖 : A
  𝑖 = value ⟦ 𝐼 ⟧₀ 𝐼↓ 

  𝑘 : A
  𝑘 = value ⟦ 𝐾 ⟧₀ 𝐾↓

  abstract
    𝑘ab≼a : (a b : A) → ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
    𝑘ab≼a a b = begin
      ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ ᶜ b ⟧ []
        ≡⟨ cong (λ t → t • pure a • pure b) (⟦⟦t⟧⟧=⟦t⟧ 𝐾 𝐾↓) ⟩
      ⟦ 𝐾 ⊙ ᶜ a ⊙ ᶜ b ⟧ []
        ≼⟨ 𝐾ab≼a a b ⟩
      ⟦ ᶜ a ⟧ []
        ∎
      where
        open ≼-Reasoning (OPCA→OPAS 𝔄)

    𝑆𝑘𝑘a≼a : (a : A) → ⟦ 𝑆 ⊙ ᶜ 𝑘 ⊙ ᶜ 𝑘 ⊙ ᶜ a ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
    𝑆𝑘𝑘a≼a a = begin
      ⟦ 𝑆 ⊙ ᶜ 𝑘 ⊙ ᶜ 𝑘 ⊙ ᶜ a ⟧ []
        ≼⟨ 𝑆abc≼acbc _ _ _ ⟩
      ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧ []
        ≡⟨ cong (λ c → c • (pure a) • (c • (pure a))) (⟦⟦t⟧⟧=⟦t⟧ 𝐾 𝐾↓) ⟩
      ⟦ 𝐾 ⊙ ᶜ a ⊙ (𝐾 ⊙ ᶜ a) ⟧ []
        ≡⟨ (λ i → ⟦ 𝐾 ⟧₀ • pure a • ƛƛ𝐾a=b i) ⟩
      ⟦ 𝐾 ⊙ ᶜ a ⊙ ᶜ value (⟦ 𝐾 ⟧₀ • pure a) (𝐾a↓ a) ⟧ []
        ≼⟨ 𝐾ab≼a a _ ⟩
      ⟦ ᶜ a ⟧ []
            ∎
      where
        open ≼-Reasoning (OPCA→OPAS 𝔄)
        𝑘¹ : A → A
        𝑘¹ a = value ⟦ 𝐾 ⊙ ᶜ a ⟧₀ (𝐾a↓ a)
        ƛƛ𝐾a=b : ⟦ (𝐾 ⊙ ᶜ a) ⟧₀ ≡ ⟦ ᶜ 𝑘¹ a ⟧₀
        ƛƛ𝐾a=b = sym (⟦⟦t⟧⟧=⟦t⟧ (𝐾 ⊙ ᶜ a) (𝐾a↓ a))

  𝑆↓ : ⟦ 𝑆 ⟧₀ ↓
  𝑆↓ = truncElim (λ _ → ⟦ 𝑆 ⟧₀ ↓-isProp) (λ a → 𝑆𝑘𝑘a≼a a tt* .fst .fst .fst .fst) nonEmpty
  
  𝑠 : A
  𝑠 = value ⟦ 𝑆 ⟧₀ 𝑆↓

  abstract
    𝑠abc≼acbc : (a b c : A) → ⟦ ᶜ 𝑠 ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧₀  ℒ≼ ⟦ (ᶜ a ⊙ ᶜ c) ⊙ (ᶜ b ⊙ ᶜ c) ⟧₀
    𝑠abc≼acbc a b c = begin
      ⟦ ᶜ 𝑠 ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧ []
        ≡⟨ cong (λ s → s • (pure a) • (pure b) • (pure c)) (⟦⟦t⟧⟧=⟦t⟧ 𝑆 𝑆↓) ⟩
      ⟦ 𝑆 ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧ []
        ≼⟨ 𝑆abc≼acbc a b c ⟩
      ⟦ (ᶜ a ⊙ ᶜ c) ⊙ (ᶜ b ⊙ ᶜ c) ⟧ []
        ∎
      where
        open ≼-Reasoning (OPCA→OPAS 𝔄)
  
