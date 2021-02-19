{-# OPTIONS --without-K --cubical #-}

module Calculus.Untyped.Confluence where

open import Prelude
  hiding (_⁺)
open import Calculus.Untyped.Base
open import Calculus.Untyped.Substitution

open import Calculus.Untyped.Progress
  using (Normal; normal-does-not-reduce)

open -↠-Reasoning

private
  variable
    Γ Δ          : Cxt
    A B C        : 𝕋
    M N L M′ N′ M₁ M₂ N₁ N₂ : Γ ⊢ A

------------------------------------------------------------------------------
-- Parallel reduction, see
-- M. Takahashi, “Parallel Reductions in λ-Calculus,” Inf. Comput., vol. 118, no. 1, pp. 120–127, 1995.

infix 3 _⇛_
data _⇛_  {Γ : Cxt} : Γ ⊢ A → Γ ⊢ A → 𝓤₀ ̇ where
  pvar : {x : A ∈ Γ}
    → `  x ⇛ ` x
  pabs
    : M ⇛ M′
      -----------
    → ƛ M ⇛ ƛ M′

  papp
    : M ⇛ M′
    → N ⇛ N′
      ----------------
    → M · N ⇛ M′ · N′

  pbeta
    : M ⇛ M′
    → N ⇛ N′
      ----------------------
    → (ƛ M) · N ⇛ M′ [ N′ ]

------------------------------------------------------------------------------
-- Transitive and Reflexive Closure of Parallel Reduction

infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_

data _⇛*_ : Γ ⊢ A → Γ ⊢ A → 𝓤₀ ̇ where
  _∎ : (M : Γ ⊢ A)
       --------
     → M ⇛* M
  _⇛⟨_⟩_
    : (L : Γ ⊢ A)
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
------------------------------------------------------------------------------
-- ⇛ is reflexive
par-refl : M ⇛ M
par-refl {M = ` _}   = pvar
par-refl {M = ƛ _}   = pabs par-refl
par-refl {M = _ · _} = papp par-refl par-refl

------------------------------------------------------------------------------
-- Sandwitch parallel reduction between single-step reduction and multi-step reduction
-- -→ ⊆ ⇛ ⊆ -↠

-→⊆⇛
  : M -→ N
  → M ⇛ N
-→⊆⇛ β         = pbeta par-refl par-refl
-→⊆⇛ (ζ M→M′)  = pabs (-→⊆⇛ M→M′)
-→⊆⇛ (ξₗ L→L′) = papp (-→⊆⇛ L→L′) par-refl
-→⊆⇛ (ξᵣ M→M′) = papp par-refl    (-→⊆⇛ M→M′)

-↠⊆⇛*
  : M -↠ N
    ------
  → M ⇛* N
-↠⊆⇛* (M ∎)          = M ∎
-↠⊆⇛* (L -→⟨ b ⟩ bs) = L ⇛⟨ -→⊆⇛ b ⟩ -↠⊆⇛* bs

⇛⊆-↠
  : M ⇛ N
  → M -↠ N
⇛⊆-↠ pvar  = _ ∎
⇛⊆-↠ (pbeta {M} {M′} {N} {N′} M⇛M′ N⇛N′) =
  (ƛ M) · N
    -↠⟨ ·-cong (ƛ-cong (⇛⊆-↠ M⇛M′)) (⇛⊆-↠ N⇛N′) ⟩
  (ƛ M′) · N′
    -→⟨ β ⟩
  M′ [ N′ ] ∎
⇛⊆-↠ (pabs M⇛N)     = ƛ-cong (⇛⊆-↠ M⇛N)
⇛⊆-↠ (papp L⇛M M⇛N) = ·-cong (⇛⊆-↠ L⇛M) (⇛⊆-↠ M⇛N)

⇛*⊆-↠
  : M ⇛* N
    ------
  → M -↠ N
⇛*⊆-↠ (M ∎)         = M ∎
⇛*⊆-↠ (L ⇛⟨ p ⟩ ps) = L -↠⟨ ⇛⊆-↠ p ⟩ ⇛*⊆-↠ ps

par-rename
  : {ρ : Rename Γ Δ}
  → M ⇛ M′
  → rename ρ M ⇛ rename ρ M′
par-rename pvar             = pvar
par-rename (pabs M⇛M′)      = pabs (par-rename M⇛M′)
par-rename (papp M⇛M′ N⇛N′) = papp (par-rename M⇛M′) (par-rename N⇛N′)
par-rename {Γ} {Δ} {ρ = ρ} (pbeta {M} {N} {M′} {N′} M⇛M′ N⇛N′) =
  let G = pbeta (par-rename {ρ = ext ρ} M⇛M′) (par-rename {ρ = ρ} N⇛N′)
  in  subst (λ L → rename ρ ((ƛ M) · M′) ⇛ L) (rename-ssubst {Γ} {Δ} ρ N N′) G

Par-Subst : Subst Γ Δ → Subst Γ Δ → Set
Par-Subst {Γ} {Δ} σ σ′ = ∀{A} {x : A ∈ Γ} → σ x ⇛ σ′ x

par-subst-exts
  : {σ σ′ : Subst Γ Δ}
  → (Par-Subst σ σ′)
  → ∀ {A} → Par-Subst (exts {Γ} {Δ} {A} σ) (exts σ′)
par-subst-exts s {x = Z _} = pvar
par-subst-exts s {x = S x} = par-rename s

par-subst
  : {σ τ : Subst Γ Δ}
  → Par-Subst σ τ
  → M ⇛ M′
  → M ⟪ σ ⟫ ⇛ M′ ⟪ τ ⟫
par-subst σ⇛τ pvar             = σ⇛τ
par-subst σ⇛τ (papp M⇛M′ N⇛N′) =
  papp (par-subst σ⇛τ M⇛M′) (par-subst σ⇛τ N⇛N′)
par-subst σ⇛τ (pabs M⇛M′) =
  pabs (par-subst (λ {A} {x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
par-subst {σ = σ} {τ} σ⇛τ (pbeta {M} {M′} {N} {N′ = N′} M⇛M′ N⇛N′) =
  let G = pbeta (par-subst {M = _} {σ = exts σ} {τ = exts τ}
            (λ{A}{x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
            (par-subst {σ = σ} σ⇛τ N⇛N′)
  in subst (λ L → (ƛ M ⟪ exts σ ⟫) · N ⟪ σ ⟫ ⇛ L) (subst-ssubst τ M′ N′) G

sub-par
  : M ⇛ M′
  → N ⇛ N′
  → M [ N ] ⇛ M′ [ N′ ]
sub-par {⋆} {Γ} {⋆} {M} {M′} {N} {N′} M⇛M′ N⇛N′ =
  par-subst {σ = subst-zero N} {τ = subst-zero N′} σ⇛σ′ M⇛M′
  where
    σ⇛σ′ : {x : A ∈ ⋆ , Γ} → subst-zero N x ⇛ subst-zero N′ x
    σ⇛σ′ {⋆} {x = Z p} = N⇛N′
    σ⇛σ′ {⋆} {x = S x} = pvar
------------------------------------------------------------------------------
-- Confluence

private
  _⁺ : Γ ⊢ A → Γ ⊢ A
  (` x) ⁺       =  ` x
  (ƛ M) ⁺       = ƛ (M ⁺)
  ((ƛ M) · N) ⁺ = M ⁺ [ N ⁺ ]
  (M · N) ⁺     = M ⁺ · (N ⁺)

  par-triangle
    : M ⇛ N
      -------
    → N ⇛ M ⁺
  par-triangle pvar = pvar
  par-triangle (pbeta M⇛M′ N⇛N′)               = sub-par (par-triangle M⇛M′) (par-triangle N⇛N′)
  par-triangle (pabs M⇛M′)                     = pabs (par-triangle M⇛M′)
  par-triangle (papp {ƛ _}   (pabs M⇛M′) N⇛N′) = pbeta (par-triangle M⇛M′) (par-triangle N⇛N′)
  par-triangle (papp {` x}   pvar        N)    = papp (par-triangle pvar)  (par-triangle N)
  par-triangle (papp {L · M} LM⇛M′       N)    = papp (par-triangle LM⇛M′) (par-triangle N)

  strip
    : M ⇛ N
    → M ⇛* N′
      ------------------------------------
    → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
  strip mn (M ∎) = ( _ , _ ∎ , mn)
  strip mn (M ⇛⟨ mm' ⟩ m'n')
    with strip (par-triangle mm') m'n'
  ... | (L , ll' , n'l') =
        (L , (_ ⇛⟨ par-triangle mn ⟩ ll') , n'l')

  par-confluence
    : L ⇛* M
    → L ⇛* M′
      ------------------------------------
    → Σ[ N ∈ Γ ⊢ A ] (M ⇛* N) × (M′ ⇛* N)
  par-confluence {Γ} {A} {L} {.L} {N} (L ∎) L⇛*N = N , L⇛*N , N ∎
  par-confluence {Γ} {A} {L} {M₁′} {M₂} (L ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂ with strip L⇛M₁ L⇛*M₂
  ... | N , M₁⇛*N , M₂⇛N with par-confluence M₁⇛*M₁′ M₁⇛*N
  ... | N′ , M₁′⇛*N′ , N⇛*N′ = N′ , M₁′⇛*N′ , (M₂ ⇛⟨ M₂⇛N ⟩ N⇛*N′)

confluence
  : L -↠ M
  → L -↠ M′
    -----------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M -↠ N) × (M′ -↠ N)
confluence L↠M₁ L↠M₂
    with par-confluence (-↠⊆⇛* L↠M₁) (-↠⊆⇛* L↠M₂)
... | N , M₁⇛N , M₂⇛N = N , ⇛*⊆-↠ M₁⇛N , ⇛*⊆-↠ M₂⇛N

Normal⇒Path : Normal M₁ → Normal M₂
  → L -↠ M₁ → L -↠ M₂
  → M₁ ≡ M₂
Normal⇒Path nM₁ nM₂ L-↠M₁ L-↠M₂ with confluence L-↠M₁ L-↠M₂
... | N , (.N ∎ , _ ∎)                          = refl
... | N , ((_ -→⟨ M₁-→M ⟩ _) , _)               = ⊥-elim (normal-does-not-reduce nM₁ M₁-→M)
... | N , (_ ∎               , _ -→⟨ M₂-→M ⟩ _) = ⊥-elim (normal-does-not-reduce nM₂ M₂-→M)
