{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude
open import Calculus.SystemT
  hiding (_,_)

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    type          : 𝕋
    _⊩_           : Prog type → X → 𝓤 ̇
    _isRealisable : Π[ x ꞉ X ] ∃[ a ꞉ Prog type ] a ⊩ x
  infix 4 _⊩_

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    X Y : Asm 𝓤
------------------------------------------------------------------------------
-- Morphisms between assemblies

module Mor (X Y : Asm 𝓤) where
  open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_)
  
  _tracks_ : (r : Prog (A →̇ B)) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  r tracks f = Π[ a ꞉ Prog A ] Π[ x ꞉ ⟨ X ⟩ ] (a ⊩x x → r · a ⊩y f x)

  HasTracker : (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  HasTracker f = Σ[ r ꞉ Prog (A →̇ B) ] r tracks f 

  Trackable : 𝓤 ̇
  Trackable = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] HasTracker f

--_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
--X ⇒ Y = Trackable , asmstr (A →̇ B) _⊩_ {!!} -- (⟨ X ⟩ → ⟨ Y ⟩) , asmstr (A →̇ B) (Mor._tracks_ X Y) {!i!}
--  where
--    open Mor X Y
--    open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_)
--    open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_)
--
--    _⊩_ : Prog (A →̇ B) → Trackable → _
--    F ⊩ (f , r , r⊩f) = Lift (F ≡ r)
------------------------------------------------------------------------------
-- Examples

_⊩⊥_ : Prog ⊤̇ → ⊥ → 𝓤₀ ̇
_⊩⊥_ = λ a ()

⊥ₐ : Asm₀
⊥ₐ = ⊥ , asmstr ⊤̇ _⊩⊥_ λ ()

-- The type (Prog A) of programs of type A is itself an assembly with α-equality
𝔗 : 𝕋 → Asm 𝓤₀
𝔗 A = Prog A , asmstr A _≡_ λ M → ∣ M , refl ∣

--_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
--X ×ₐ Y = ⟨ X ⟩ × ⟨ Y ⟩ , asmstr (A ×̇ B) _⊩_ realisable
--  where
--    open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_; _isRealisable to _isRealisable₁)
--    open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_; _isRealisable to _isRealisable₂)
--
--    _⊩_ : Prog (A ×̇ B) → ⟨ X ⟩ × ⟨ Y ⟩ → _ ̇
--    L ⊩ (x , y) = (projₗ L ⊩x x) × (projᵣ L ⊩y y)
--
--    realisable : Π[ z ꞉ ⟨ X ⟩ × ⟨ Y ⟩ ] ∃[ a ꞉ Prog (A ×̇ B) ] a ⊩ z
--    realisable (x , y) = rec propTruncIsProp (rec (isPropΠ (λ _ → propTruncIsProp))
--      (λ { (N , N⊩y) (M , M⊩x) → ∣ {!!} ,  ∣ }) (y isRealisable₂)) (x isRealisable₁)
  
-- ∇₀_ : (X : 𝓤 ̇) → Asm 𝓤
-- ∇₀ X = X , asmstr {!!} _⊩∇_ ⊩∇-is-a-realisabiltiy
--   where
--     _⊩∇_ : Prog {!!} → X → (universe-of X) ̇
--     a ⊩∇ x = Unit*

--     ⊩∇-is-a-realisabiltiy : Π[ x ꞉ X ] ∃[ a ꞉ Prog {!!} ] a ⊩∇ x
--     ⊩∇-is-a-realisabiltiy x =
--       truncElim {P = λ _ → ∃[ a ꞉ Prog {!!} ] Unit*} (λ _ → propTruncIsProp)
--       (λ a → ∣ a , tt* ∣) {!!}
