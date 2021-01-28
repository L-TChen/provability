{-# OPTIONS --without-K --cubical #-}
module Algebra.OPCA.Properties where

open import Prelude
  hiding (_≡⟨_⟩_)
open import Algebra.OPCA.Base
import      Algebra.OPAS.Properties as OPASₚ

module _ (𝔄 : OPCA 𝓥 𝓤) where
  open OpcaStr (str 𝔄) renaming (⟦_⟧_ to ⟦_⟧ᵗ_)
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

  private
    -- I = λ x. x
    𝐼 : Term (suc n)
    𝐼 = ` 0
    -- K = λ x. λy. x
    𝐾 : Term (2 + n)
    𝐾 = ` 1
    -- S = λ x. λ y. λ z. xz(yz)
    𝑆 : Term (3 + n)
    𝑆 = ` 2 ⊙ ` 0 ⊙ (` 1 ⊙ ` 0)

    abstract
      𝐼a≼a : (a : A) → ⟦ (ƛ 𝐼) ⊙ ᶜ a ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
      𝐼a≼a a = completeness
      
      𝐾ab≼a : ∀ a b
        → ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
      𝐾ab≼a a b = begin
        ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ ᶜ b ⟧ []
          ≼⟨ •ₗ-respect-ℒ≼ ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⟧₀ (⟦ ƛ 𝐾 ⟧ᵗ [ a ]) (pure b) completeness ⟩
        ⟦ (ƛ 𝐾) ⊙ ᶜ b ⟧ [ a ]
          ≼⟨ completeness  ⟩
        ⟦ 𝐾 ⟧ b ∷ [ a ]
          ∎
        where open ≼-Reasoning (OPCA→OPAS 𝔄)
        
      𝑆abc≼acbc : ∀ a b c → ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧₀ ℒ≼ ⟦ ᶜ a ⊙ ᶜ c ⊙ (ᶜ b ⊙ ᶜ c) ⟧₀
      𝑆abc≼acbc a b c = begin
        ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ a ⊙ ᶜ b ⊙ ᶜ c ⟧ []
          ≼⟨ •ₗ-respect-ℒ≼ ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ a ⊙ ᶜ b ⟧₀ (⟦ (ƛ ƛ 𝑆) ⊙ ᶜ b ⟧ᵗ _)  (pure c)
            (•ₗ-respect-ℒ≼ ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ a ⟧₀ (⟦ ƛ ƛ 𝑆 ⟧ᵗ _) (pure b) completeness) ⟩
        ⟦ (ƛ ƛ 𝑆) ⊙ ᶜ b  ⊙ ᶜ c ⟧ [ a ]
          ≼⟨ •ₗ-respect-ℒ≼ (⟦ (ƛ ƛ 𝑆) ⊙ ᶜ b ⟧ᵗ _) (⟦ ƛ 𝑆 ⟧ᵗ _) (pure c) completeness ⟩
        ⟦ (ƛ 𝑆) ⊙ ᶜ c ⟧ b ∷ [ a ]
          ≼⟨ completeness ⟩
        ⟦ 𝑆 ⟧ c ∷ b ∷ [ a ]
          ∎
        where open ≼-Reasoning (OPCA→OPAS 𝔄)

      𝐼a↓ : (a : A) → ⟦ (ƛ 𝐼) ⊙ ᶜ a ⟧₀ ↓
      𝐼a↓ a = 𝐼a≼a a tt* .fst

      𝐼↓ : ⟦ ƛ 𝐼 ⟧₀ ↓
      𝐼↓ = truncElim (λ _ → ⟦ ƛ 𝐼 ⟧₀ ↓-isProp) (fst ∘ 𝐼a↓) nonEmpty 

      𝐾ab↓ : (a b : A) → ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ ᶜ b ⟧₀ ↓
      𝐾ab↓ a b = 𝐾ab≼a a b _ .fst

      𝐾a↓ : (a : A) → ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⟧₀ ↓
      𝐾a↓ a = 𝐾ab↓ a a .fst

      𝐾↓ : ⟦ ƛ ƛ 𝐾 ⟧₀ ↓
      𝐾↓ = truncElim (λ _ → ⟦ ƛ ƛ 𝐾 ⟧₀ ↓-isProp) (fst ∘ 𝐾a↓) nonEmpty

  𝑖¹ : A → A
  𝑖¹ a = value ⟦ (ƛ 𝐼) ⊙ ᶜ a ⟧₀ (𝐼a↓ _)

  𝑖 : A
  𝑖 = value ⟦ ƛ 𝐼 ⟧₀ 𝐼↓ 

  𝑘¹ : A → A
  𝑘¹ a = value ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⟧₀ (𝐾a↓ a)
  
  𝑘 : A
  𝑘 = value ⟦ ƛ ƛ 𝐾 ⟧₀ 𝐾↓

  𝑘ab≼a : (a : A) → ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
  𝑘ab≼a a = begin
    ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧ []
      ≡⟨ cong (λ c → c • (pure a) • (c • (pure a))) 𝑘=ƛƛ𝐾 ⟩
    ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ ((ƛ ƛ 𝐾) ⊙ ᶜ a) ⟧ []
      ≡⟨ (λ i → ⟦ ƛ ƛ 𝐾 ⟧₀ • pure a • ƛƛ𝐾a=b i) ⟩
    ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ ᶜ value (⟦ ƛ ƛ 𝐾 ⟧₀ • pure a) (𝐾a↓ a) ⟧ []
      ≼⟨ 𝐾ab≼a a _ ⟩
    ⟦ ᶜ a ⟧ []
      ∎
    where
      open ≼-Reasoning (OPCA→OPAS 𝔄)
      abstract
        𝑘=ƛƛ𝐾 : ⟦ ᶜ 𝑘 ⟧₀ ≡ ⟦ ƛ ƛ 𝐾 ⟧₀
        𝑘=ƛƛ𝐾 = ⟦⟦t⟧⟧=⟦t⟧ (ƛ ƛ 𝐾) 𝐾↓
        ƛƛ𝐾a=b : ⟦ ((ƛ ƛ 𝐾) ⊙ ᶜ a) ⟧₀ ≡ ⟦ ᶜ 𝑘¹ a ⟧₀
        ƛƛ𝐾a=b = sym (⟦⟦t⟧⟧=⟦t⟧ ((ƛ ƛ 𝐾) ⊙ ᶜ a) (𝐾a↓ a))

  𝑆↓ : ⟦ ƛ ƛ ƛ 𝑆 ⟧₀ ↓
  𝑆↓ = truncElim (λ _ → ⟦ ƛ ƛ ƛ 𝑆 ⟧₀ ↓-isProp) (λ a → lemma a tt* .fst .fst .fst .fst) nonEmpty
    where
      open ≼-Reasoning (OPCA→OPAS 𝔄)
      lemma : (a : A) → ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ 𝑘 ⊙ ᶜ 𝑘 ⊙ ᶜ a ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
      lemma a = begin
        ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ 𝑘 ⊙ ᶜ 𝑘 ⊙ ᶜ a ⟧ []
          ≼⟨ 𝑆abc≼acbc _ _ _ ⟩
        ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧ []
          ≼⟨ 𝑘ab≼a _ ⟩
        ⟦ ᶜ a ⟧ []
          ∎
  
  𝑠 : A
  𝑠 = value ⟦ ƛ ƛ ƛ 𝑆 ⟧₀ 𝑆↓
