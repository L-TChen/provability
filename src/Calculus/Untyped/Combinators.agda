{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Combinators where

open import Prelude

open import Calculus.Untyped.Base
open import Calculus.Untyped.Substitution

private
  variable
    A B C : 𝕋
    M N L : Γ ⊢ A

infix 9 `⟨_,_⟩

------------------------------------------------------------------------------
-- Some combinators

Λ₀ : 𝓤₀ ̇
Λ₀ = ∅ ⊢ ⋆

𝑰 𝑲 𝑻 𝑭 : Λ₀
𝑰 = ƛ 0
𝑲 = ƛ ƛ 1
𝑻 = 𝑲
𝑭 = ƛ ƛ 0

`⟨_,_⟩ : (M N : Λ₀) → Λ₀
`⟨ M , N ⟩ = ƛ 0 · ↑ M · ↑ N

`projₗ : Λ₀ → Λ₀ 
`projₗ M = M · 𝑻

`projᵣ : Λ₀ → Λ₀ 
`projᵣ M = M · 𝑭

------------------------------------------------------------------------------
-- Church endoing of naturals

pre𝒄_ : ℕ → ⋆ , ⋆ , ∅ ⊢  ⋆
pre𝒄 zero    = 0
pre𝒄 (suc n) = 1 · pre𝒄 n

𝒄_ : ℕ → Λ₀
𝒄 n = ƛ ƛ pre𝒄 n 
------------------------------------------------------------------------------
-- Examples

β-projₗ : `projₗ `⟨ M , N ⟩ -↠ M
β-projₗ {M} {N} = begin
  `projₗ `⟨ M , N ⟩
    -→⟨ β ⟩
  𝑻 · ↑ M [ 𝑻 ] · ↑ N [ 𝑻 ]
    ≡⟨ cong₂ (λ M N → 𝑻 · M · N) (subst-↑ _ M) (subst-↑ _ N) ⟩
  𝑻 · M · N
    -→⟨ ξₗ β ⟩
  (ƛ 1) [ M ]  · N
    -→⟨ β ⟩
  ↑₁ M [ N ]
    ≡⟨ subst-rename-∅ _ _ M ⟩
  M ∎
  where open -↠-Reasoning

β-projᵣ : `projᵣ `⟨ M , N ⟩ -↠ N
β-projᵣ {M} {N} = begin
  `projᵣ `⟨ M , N ⟩
    -→⟨ β ⟩
  𝑭 · ↑ M [ 𝑭 ] · ↑ N [ 𝑭 ]
    ≡⟨ cong₂ (λ M N → 𝑭 · M · N) (subst-↑ _ M) (subst-↑ _ N) ⟩
  𝑭 · M · N
    -→⟨ ξₗ β ⟩
  (ƛ 0) [ M ]  · N
    -→⟨ β ⟩
  N ∎
  where open -↠-Reasoning
