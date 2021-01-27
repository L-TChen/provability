{-# OPTIONS --without-K --cubical --allow-unsolved-metas #-}
module Algebra.OPAS.Properties where

open import Prelude
open import Algebra.OPAS.Base

module Structure (𝔄 : OPAS 𝓥 𝓤) where
  open OpasStr (str 𝔄)

  private
    A = ⟨ 𝔄 ⟩

  •ₗ-respect-ℒ≼ : (x₀ x₁ y : ℒ 𝓥 A) → x₀ ℒ≼ x₁  → x₀ • y ℒ≼ x₁ • y
  •ₗ-respect-ℒ≼ _ _ _ x₀≼ᵖx₁ (x₁↓ , y↓ , xy↓) =
    (x₀↓ , y↓ , xz≼yz .fst) , xz≼yz .snd
    where
      x₀↓   = x₀≼ᵖx₁ x₁↓ .fst
      x₀≼x₁ = x₀≼ᵖx₁ x₁↓ .snd
      xz≼yz = ·-respect-≼ x₀≼x₁ (≼-isReflexive _) xy↓

  •ᵣ-respect-ℒ≼ : (x y₀ y₁ : ℒ 𝓥 A) → y₀ ℒ≼ y₁ → x • y₀ ℒ≼ x • y₁
  •ᵣ-respect-ℒ≼ _ _ _ y₀≼ᵖy₁ (x↓ , y₁↓ , xy↓) =
    (x↓ , y₀↓ , xy≼xz .fst) , xy≼xz .snd
    where
      y₀↓   = y₀≼ᵖy₁ y₁↓ .fst
      y₀≼y₁ = y₀≼ᵖy₁ y₁↓ .snd
      xy≼xz = ·-respect-≼ (≼-isReflexive _) y₀≼y₁ xy↓

  •-respect-ℒ≼ : (x₀ y₀ x₁ y₁ : ℒ 𝓥 A) → x₀ ℒ≼ x₁ → y₀ ℒ≼ y₁ → x₀ • y₀ ℒ≼ x₁ • y₁
  •-respect-ℒ≼ _ _ _ _ x₀≼ᵖx₁ y₀≼ᵖy₁ (x₁↓ , y₁↓ , xy↓) =
    (x₀↓ , y₀↓ , ·-respect-≼ x₀≼x₁ y₀≼y₁ xy↓ .fst) , ·-respect-≼ x₀≼x₁ y₀≼y₁ xy↓ .snd
    where
      x₀↓   = x₀≼ᵖx₁ x₁↓ .fst
      x₀≼x₁ = x₀≼ᵖx₁ x₁↓ .snd
      y₀↓   = y₀≼ᵖy₁ y₁↓ .fst
      y₀≼y₁ = y₀≼ᵖy₁ y₁↓ .snd

  ⟦⟦t⟧⟧=⟦t⟧ : (t : Term 0) → (t↓ : ⟨ ⟦ t ⟧₀ ↓ ⟩) → ⟦ ᶜ value ⟦ t ⟧₀ t↓ ⟧₀ ≡ ⟦ t ⟧₀
  ⟦⟦t⟧⟧=⟦t⟧ t t↓ = 
    ⟦ ᶜ value ⟦ t ⟧₀ t↓ ⟧₀
      ≡⟨ refl ⟩
    pure (value ⟦ t ⟧₀ t↓ )
      ≡⟨ refl ⟩
    (Unit* , isPropUnit*) , (λ _ → value ⟦ t ⟧₀ t↓)
      ≡⟨ {!!} ⟩ 
    (⟦ t ⟧₀ ↓) , value ⟦ t ⟧₀
      ≡⟨ refl ⟩
    ⟦ t ⟧₀
      ∎
