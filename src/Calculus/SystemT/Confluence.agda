{-# OPTIONS --without-K --cubical #-}

-- System T

module Calculus.SystemT.Confluence where

open import Prelude
open import Calculus.SystemT.Base

private
  variable
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
... | N , ((.N ∎) , (_ ∎))                       = refl
... | N , ((_ -→⟨ M₁-→M ⟩ _) , _)                 = ⊥-elim (nM₁ (_ , M₁-→M))
... | N , ((_ ∎)             , (_ -→⟨ M₂-→M ⟩ _)) = ⊥-elim (nM₂ (_ , M₂-→M) )
