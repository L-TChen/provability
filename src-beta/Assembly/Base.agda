{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped
  hiding (Z)

record IsRealisability {X : 𝓤 ̇} (_⊩_ : Λ₀ → X → 𝓤 ̇) : 𝓤 ̇ where
  field
    ⊩-respects-↠  : _⊩_ respects _-↠_ on-the-left
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
Asm 𝓤 = SetWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

------------------------------------------------------------------------------
-- Morphisms between assemblies

Tracks : (X Y : Asm 𝓤)
  → Λ₁ → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →       M X.⊩ x
  → F [ M ] Y.⊩ f x
  where
    module X = AsmStr (strₛ X)
    module Y = AsmStr (strₛ Y)

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor _,_

  module X = AsmStr (strₛ X)
  module Y = AsmStr (strₛ Y)

  field
    F   : Λ₁
    F⊩f : Tracks X Y F f

Trackable : (X Y : Asm 𝓤) → 𝓤 ̇
Trackable X Y = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] HasTracker X Y f

MerelyTrackable : (X Y : Asm 𝓤) → 𝓤 ̇
MerelyTrackable X Y = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥
------------------------------------------------------------------------------
-- Extensional equality between morphisms

-- Partial equivalence relation
record PER {X : 𝓤 ̇} (_∼_ : X → X → 𝓤 ̇) : 𝓤 ⁺ ̇ where
  field
    symmetric  : {x y : X}
      → x ∼ y → y ∼ x
    transitive : {x y z : X}
      → x ∼ y → y ∼ z → x ∼ z
      
∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , _) (g , _) = (x : ⟨ X ⟩) → f x ≡ g x

∼-is-PER : {X Y : Asm 𝓤}
  → PER (∼-eq X Y)
∼-is-PER = record
  { symmetric  = λ { {f , _} {g , _}         f=g x     → sym (f=g x) }
  ; transitive = λ { {f , _} {g , _} {h , _} f=g g=h x → f=g x ∙ g=h x }
  }

infix 4 ∼-syntax

syntax ∼-syntax {X = X} {Y = Y} f g = f ∼ g ꞉ X →ₐ Y

∼-syntax : {X Y : Asm 𝓤} → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

id : (X : Asm 𝓤) → Trackable X X
id X = 𝓤.id , 0 , 𝓤.id

infixr 9 _∘_

_∘_ : {X Y Z : Asm 𝓤}
  → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {Z = Z} (g , G , G⊩g) (f , F , F⊩f) = g 𝓤.∘ f , (G ∘′ F) , λ {_} {x} M⊩x →
  subst (Z._⊩ g (f x)) (∘-ssubst-ssubst G F _ ⁻¹) (G⊩g (F⊩f M⊩x))
    where module Z = AsmStr (strₛ Z)

AsmIso : (X Y : Asm 𝓤) → (Trackable X Y) → 𝓤 ̇
AsmIso X Y f = ∃[ g ꞉ Trackable Y X ] (f ∘ g ∼ id Y ꞉ Y →ₐ Y) × (g ∘ f ∼ id X ꞉ X →ₐ X)
