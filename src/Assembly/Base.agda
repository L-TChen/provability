{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude
  hiding (_∎; _∘_; _≡⟨_⟩_; ≡⟨⟩-syntax)
open import Calculus.SystemT
  renaming (_,_ to _ctx,_)

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    type          : 𝕋
    _⊩_           : Prog type → X → 𝓤 ̇
    _isRealisable : Π[ x ꞉ X ] ∃[ M ꞉ Prog type ] M ⊩ x
  infix 4 _⊩_

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Morphisms between assemblies

module Mor (X Y : Asm 𝓤) where
  open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_)
  
  _tracks_ : (F : Prog (A →̇ B)) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  F tracks f = Π[ M ꞉ Prog A ] Π[ x ꞉ ⟨ X ⟩ ] (M ⊩x x → Σ[ N ꞉ Prog B ] (F · M -↠ N) × (N ⊩y f x))

  HasTracker : (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  HasTracker f = Σ[ r ꞉ Prog (A →̇ B) ] r tracks f 

  Trackable : 𝓤 ̇
  Trackable = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] HasTracker f
open Mor

idₐ : (X : Asm 𝓤) → Trackable X X
idₐ (|X| , asmX) = id , ƛ # 0 , λ M x M⊩x → M , ((ƛ # 0) · M -→⟨ β-ƛ· ⟩ M ∎) , M⊩x
  where open -↠-Reasoning

infixr 9 _∘_
_∘_ : {X Y Z : Asm 𝓤} → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {X = X} {Y} {Z} (g , G , G⊩g) (f , F , F⊩f) = (λ x → g (f x)) , ƛ ↑ G · (↑ F · # 0) , GF⊩gf
  where
    open -↠-Reasoning
    open Mor X Y renaming (_tracks_ to _tracksXY_)
    open Mor Y Z renaming (_tracks_ to _tracksYZ_)
    open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_)
    open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_)
    open AsmStr (str Z) renaming (type to C; _⊩_ to _⊩z_)
    GF⊩gf : ∀ M x → M ⊩x x → Σ[ L ꞉ Prog C ] ((ƛ ↑ G · (↑ F · # 0)) · M -↠ L) × (L ⊩z g (f x))
    GF⊩gf M x M⊩x = L , red , L⊩gfx
      where
        N : Prog B
        N = F⊩f M x M⊩x .fst
        N⊩fx : N ⊩y (f x)
        N⊩fx =  F⊩f M x M⊩x .snd .snd

        L : Prog C
        L = G⊩g N (f x) N⊩fx .fst
        L⊩gfx : L ⊩z (g (f x))
        L⊩gfx = G⊩g N (f x) N⊩fx .snd .snd
        
        red : (ƛ ↑ G · (↑ F · # 0)) · M -↠ L -- G · (F · M) 
        red = begin
          (ƛ ↑ G · (↑ F · # 0)) · M
            -→⟨ β-ƛ· ⟩
          ↑ G ⟪ _ ⟫ · (↑ F ⟪ _ ⟫ · M)
            ≡⟨ cong₂ (λ N L → N · (L · M)) (subst-↑ _ G) (subst-↑ _ F) ⟩ 
          G · (F · M)
            -↠⟨ ·ᵣ-↠ (F⊩f M x M⊩x .snd .fst) ⟩
          G · N
            -↠⟨ G⊩g N (f x) N⊩fx .snd .fst ⟩
          L
            ∎ 

------------------------------------------------------------------------------
-- Constructions

-- TODO: show that ⊥ is initial
⊥ₐ : (A : 𝕋) → Asm₀
⊥ₐ A = ⊥ , asmstr A (λ _ ()) λ ()

ℕₐ : Asm₀
ℕₐ = ℕ , asmstr nat _⊩_ realisable
  where
    _⊩_ : Prog nat → ℕ → 𝓤₀ ̇
    zero    ⊩ 0       = Unit
    (suc M) ⊩ (suc n) = M ⊩ n
    _       ⊩ _       = ⊥

    realisable : Π[ n ꞉ ℕ ] ∃[ M ꞉ Prog nat ] (M ⊩ n)
    realisable zero    = ∣ zero , tt ∣
    realisable (suc n) = rec propTruncIsProp (λ { (M , M⊩n) → ∣ suc M , M⊩n ∣}) (realisable n)
    

--_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
--X ⇒ Y = Trackable , asmstr (A →̇ B) _⊩_ {!!} -- (⟨ X ⟩ → ⟨ Y ⟩) , asmstr (A →̇ B) (Mor._tracks_ X Y) {!i!}
--  where
--    open Mor X Y
--    open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_)
--    open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_)
--
--    _⊩_ : Prog (A →̇ B) → Trackable → _
--    F ⊩ (f , r , r⊩f) = Lift (F ≡ r)

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


--Exposure : (𝓤 : Universe) → 𝓤 ⁺ ̇
--Exposure 𝓤 = Σ[ 𝔔 ꞉ (Asm 𝓤 → Asm 𝓤) ] Σ[ 𝔔₁ ꞉ (∀ X Y → Trackable {𝓤} X Y → Trackable {𝓤} (𝔔 X) (𝔔 Y) ) ] {!!} 
