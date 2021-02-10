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
`⟨ M , N ⟩ = ƛ 0 · ↑₁ M · ↑₁ N

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

postulate
  β-projₗ : `projₗ `⟨ M , N ⟩ -↠ M
--β-projₗ {M} {N} = begin
--  `projₗ `⟨ M , N ⟩
--    ≡⟨ refl ⟩
--  (ƛ 0 · ↑₁ M · ↑₁ N) · 𝑻
--    -→⟨ β ⟩
--  0 [ 𝑻 ] · ↑₁ M [ 𝑻 ] · ↑₁ N [ 𝑻 ]
--    ≡⟨ {!!} ⟩
--  𝑻 · M · N 
--    -→⟨ ξₗ β ⟩
--  (ƛ 1) [ M ] · N
--    ≡⟨ {!!} ⟩
--  (ƛ ↑₁ M) · N
--    -→⟨ β ⟩ 
--  ↑₁ M [ N ]
--    ≡⟨ subst-rename-∅ S_ _ M ⟩
--  M ∎
--  where open -↠-Reasoning

postulate
  β-projᵣ : `projᵣ `⟨ M , N ⟩ -↠ N
--β-projᵣ {M} {N} = {!!}
--  where open -↠-Reasoning
