{-# OPTIONS --without-K --cubical --guarded #-}

module Calculus.Untyped.Combinators where

open import Prelude

open import Calculus.Untyped.Base
open import Calculus.Untyped.Substitution

private
  variable
    Γ Δ   : Cxt
    A B C : 𝕋
    M N L : Γ ⊢ A

infix 9 `⟨_,_⟩

------------------------------------------------------------------------------
-- Some combinators

Λ₀ Λ₁ : 𝓤₀ ̇
Λ₀ = ∅ ⊢ ⋆
Λ₁ = ⋆ , ∅ ⊢ ⋆

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

β-projₗ : `projₗ `⟨ M , N ⟩ -↠ M
β-projₗ {M} {N} = begin
  (ƛ 0 · ↑₁ M · ↑₁ N) · 𝑻
    -→⟨ β ⟩
  𝑻 · ↑₁ M [ 𝑻 ] · ↑₁ N [ 𝑻 ]
    -→⟨ ξₗ β ⟩
  (ƛ 1) [ ↑₁ M [ 𝑻 ] ] · ↑₁ N [ 𝑻 ]
    ≡⟨ cong₂ {C = λ _ _ → Λ₀} _·_ (cong {B = λ _ → Λ₀} (ƛ_ ∘ ↑₁_) (subst-rename-∅ _ M)) (subst-rename-∅ _ N) ⟩
  (ƛ ↑₁ M) · N
    -→⟨ β ⟩
  ↑₁ M [ N ]
    ≡⟨ subst-rename-∅ _ M ⟩
  M ∎
  where open -↠-Reasoning

β-projᵣ : `projᵣ `⟨ M , N ⟩ -↠ N
β-projᵣ {M} {N} = begin
  (ƛ 0 · ↑₁ M · ↑₁ N) · 𝑭
    -→⟨ β ⟩
  𝑭 · ↑₁ M [ 𝑭 ] · ↑₁ N [ 𝑭 ]
    -→⟨ ξₗ β ⟩
  (ƛ 0) · ↑₁ N [ 𝑭 ]
    -→⟨ β ⟩
  ↑₁ N [ 𝑭 ]
    ≡⟨ subst-rename-∅ _ N ⟩
  N ∎
  where open -↠-Reasoning
