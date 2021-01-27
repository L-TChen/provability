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

      𝐼↓ : ⟦ ƛ 𝐼 ⟧₀ ↓
      𝐼↓ = truncElim (λ _ → ⟦ ƛ 𝐼 ⟧₀ ↓isProp) (λ a → 𝐼a≼a a tt* .fst .fst ) nonEmpty 

      𝐾↓ : ⟦ ƛ ƛ 𝐾 ⟧₀ ↓ 
      𝐾↓ = truncElim (λ _ → ⟦ ƛ ƛ 𝐾 ⟧₀ ↓isProp) (λ a → 𝐾ab≼a a a _ .fst .fst .fst) nonEmpty

  𝑖 : A
  𝑖 = value ⟦ ƛ 𝐼 ⟧₀ 𝐼↓ 

  𝑘 : A
  𝑘 = value ⟦ ƛ ƛ 𝐾 ⟧₀ 𝐾↓

  postulate
    𝑘ab≼a : (a b : A) → ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
    --𝑘ab≼a a b = begin
    --  ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧ []
    --    ≡⟨ {!!} ⟩
    --  ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧ []
    --    ≡⟨ {!!} ⟩
    --  ⟦ (ƛ ƛ 𝐾) ⊙ ᶜ a ⊙ (ᶜ 𝑘¹ a) ⟧ []
    --    ≼⟨ 𝐾ab≼a a (𝑘¹ a)  ⟩
    --  ⟦ ᶜ a ⟧ []
    --    ∎
    --  where
    --    open ≼-Reasoning (OPCA→OPAS 𝔄)

  𝑆↓ : ⟦ ƛ ƛ ƛ 𝑆 ⟧₀ ↓
  𝑆↓ = truncElim (λ _ → ⟦ ƛ ƛ ƛ 𝑆 ⟧₀ ↓isProp) (λ a → lem a _ .fst .fst .fst .fst) nonEmpty
    where
      open ≼-Reasoning (OPCA→OPAS 𝔄)
      lem : (a : A) → ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ 𝑘 ⊙ ᶜ 𝑘 ⊙ ᶜ a ⟧₀ ℒ≼ ⟦ ᶜ a ⟧₀
      lem a = begin
        ⟦ (ƛ ƛ ƛ 𝑆) ⊙ ᶜ 𝑘 ⊙ ᶜ 𝑘 ⊙ ᶜ a ⟧ []
          ≼⟨ 𝑆abc≼acbc _ _ _ ⟩
        ⟦ ᶜ 𝑘 ⊙ ᶜ a ⊙ (ᶜ 𝑘 ⊙ ᶜ a) ⟧ []
          ≼⟨ 𝑘ab≼a _ (value ⟦ ᶜ 𝑘 ⊙ ᶜ a ⟧₀ (𝑘ab≼a a a tt* .fst .snd .fst)) ⟩
        ⟦ ᶜ a ⟧ []
          ∎
  
  𝑠 : A
  𝑠 = value ⟦ ƛ ƛ ƛ 𝑆 ⟧₀ 𝑆↓
