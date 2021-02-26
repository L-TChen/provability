{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped
  hiding (Z)

record IsRealisability {X : 𝓤 ̇} (_⊩_ : Λ₀ → X → 𝓤 ̇) : 𝓤 ̇ where
  field
    ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
    ⊩-right-total : _⊩_ IsRightTotal
    -- ⊩-isProp     : Π[ M ꞉ Λ₀ ] Π[ x ꞉ X ] isProp (M ⊩ x)
    -- ⊩-isProp is useful when defining □, but however it does not seem necessary to define ASM?

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    _⊩_             : Λ₀ → X → 𝓤 ̇
    isRealisability : IsRealisability _⊩_
  open IsRealisability isRealisability public
  infix 6 _⊩_

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

------------------------------------------------------------------------------
-- Morphisms between assemblies

Tracks : (X Y : Asm 𝓤)
  → Λ₁ → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →       M X.⊩ x
  → F [ M ] Y.⊩ f x
  -- TODO: Clarify if this needs to be ∥ ... ∥
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor _,_

  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  field
    F   : Λ₁
    F⊩f : Tracks X Y F f

Trackable : (X Y : Asm 𝓤) → 𝓤 ̇
Trackable X Y = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] HasTracker X Y f
 
------------------------------------------------------------------------------
-- Extensional equality between morphisms

∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , _) (g , _) = (x : ⟨ X ⟩) → f x ≡ g x

infix 4 ∼-syntax

syntax ∼-syntax {X = X} {Y = Y} f g = f ∼ g ꞉ X →ₐ Y

∼-syntax : {X Y : Asm 𝓤} → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

id : (X : Asm 𝓤) → Trackable X X
id X = 𝓤.id , 0 , 𝓤.id

infixr 9 _∘_

-- TODO: Clarify this definition.
_∘_ : {X Y Z : Asm 𝓤}
  → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {Z = Z} (g , G , G⊩g) (f , F , F⊩f) = g 𝓤.∘ f , (G ∘′ F) , λ {_} {x} M⊩x →
  subst (Z._⊩ g (f x)) (∘-ssubst-ssubst G F _ ⁻¹) (G⊩g (F⊩f M⊩x))
    where module Z = AsmStr (str Z)
