{-# OPTIONS --without-K --cubical #-}

-- System T

module Calculus.SystemT.Confluence where

open import Prelude
  hiding (_,_; ⟨_⟩; ⟪_⟫; _∎; _≡⟨_⟩_; ≡⟨⟩-syntax)

open import Calculus.Type           public
open import Calculus.Context        public
open import Calculus.SystemT.Base   public


private
  variable
    Γ Δ          : Cxt
    A B C        : 𝕋
    M N L M₁ M₂  : Γ ⊢ A

postulate
  confluence
    : L -↠ M₁
    → L -↠ M₂
      -----------------------------------
    → Σ[ N ∈ Γ ⊢ A ] (M₁ -↠ N) × (M₂ -↠ N)
