{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Confluence where

open import Prelude
open import Calculus.Untyped.Base
open import Calculus.Untyped.Progress
  using (Normal; normal-does-not-reduce)

private
  variable
    Γ            : Cxt 
    A B C        : 𝕋
    M N L M₁ M₂  : Γ ⊢ A

postulate
  confluence
    : L -↠ M₁
    → L -↠ M₂
      -----------------------------------
    → Σ[ N ∈ Γ ⊢ A ] (M₁ -↠ N) × (M₂ -↠ N)

open -↠-Reasoning
Normal⇒Path : Normal M₁ → Normal M₂
  → L -↠ M₁ → L -↠ M₂
  → M₁ ≡ M₂
Normal⇒Path nM₁ nM₂ L-↠M₁ L-↠M₂ with confluence L-↠M₁ L-↠M₂
... | N , (.N ∎ , _ ∎)                          = refl
... | N , ((_ -→⟨ M₁-→M ⟩ _) , _)               = ⊥-elim (normal-does-not-reduce nM₁ M₁-→M)
... | N , (_ ∎               , _ -→⟨ M₂-→M ⟩ _) = ⊥-elim (normal-does-not-reduce nM₂ M₂-→M)
