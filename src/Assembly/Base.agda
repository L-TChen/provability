{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped

record IsRealisability {X : 𝓤 ̇} (_⊩_ : Λ₀ → X → 𝓤 ̇) : 𝓤 ̇ where
  field
    ⊩-respects-↠  : _⊩_ respects _-↠_ on-the-left
    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-isSet       : ∀ {M x} → isSet (M ⊩ x)
    -- ⊩-isProp     : Π[ M ∶ Λ₀ ] Π[ x ∶ X ] isProp (M ⊩ x)
    -- ⊩-isProp is useful when defining □, but however it does not seem necessary to define ASM?

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    _⊩_           : Λ₀ → X → 𝓤 ̇
    realisability : IsRealisability _⊩_
  open IsRealisability realisability public
  infix 6 _⊩_

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = SetWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Morphisms between assemblies

Tracks : (X Y : Asm 𝓤)
  → Λ₁ → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →       M X.⊩ x
  → F [ M ] Y.⊩ f x
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor _,_

  field
    F   : Λ₁
    F⊩f : Tracks X Y F f

--HasTracker : (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
--HasTracker X Y f = Σ[ F ∶ Λ₁ ] Tracks X Y F f

Trackable : (X Y : Asm 𝓤) → 𝓤 ̇
Trackable X Y = Σ[ f ∶ ⟨ X ⟩ ➝ ⟨ Y ⟩ ] HasTracker X Y f

MerelyTrackable : (X Y : Asm 𝓤) → 𝓤 ̇
MerelyTrackable X Y = Σ[ f ∶ ⟨ X ⟩ ➝ ⟨ Y ⟩ ] ∥ HasTracker X Y f ∥

------------------------------------------------------------------------------
-- Extensional equality between morphisms

-- Partial equivalence mere relation
record isPER {X : 𝓤 ̇} (_∼_ : Rel X X) : 𝓤 ⁺ ̇ where
  field
    symmetric  : {x y : X}
      → x ∼ y → y ∼ x
    transitive : {x y z : X}
      → x ∼ y → y ∼ z → x ∼ z
    is-prop : (x y : X) → isProp (x ∼ y)
      
∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , _) (g , _) = ∀ x → f x ≡ g x

∼-syntax : {X Y : Asm 𝓤} → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

infix 4 ∼-syntax
syntax ∼-syntax f g = f ∼ g 

∼-isProp : (f g : Trackable X Y) → isProp (∼-eq X Y f g)
∼-isProp {X = X} {Y} (f , _ , _) (g , _ , _) = isPropΠ λ _ → (Y is-set) _ _
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

∼-is-PER : {X Y : Asm 𝓤}
  → isPER (∼-eq X Y)
∼-is-PER = record
  { symmetric  = λ { {f , _} {g , _}         f=g     x → sym (f=g x) }
  ; transitive = λ { {f , _} {g , _} {h , _} f=g g=h x → f=g x ∙ g=h x }
  ; is-prop    = ∼-isProp 
  }

id : (X : Asm 𝓤) → Trackable X X
id X = 𝓤.id , 0 , 𝓤.id

infixr 9 _∘_

_∘_ : {X Y Z : Asm 𝓤}
  → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {Z = Z} (g , G , G⊩g) (f , F , F⊩f) = g 𝓤.∘ f , (G ∘′ F) , λ {_} {x} M⊩x →
  subst (Z._⊩ g (f x)) (∘-ssubst-ssubst G F _ ⁻¹) (G⊩g (F⊩f M⊩x))
    where module Z = AsmStr (str Z)

AsmIso : (X Y : Asm 𝓤) → (Trackable X Y) → 𝓤 ̇
AsmIso X Y f = ∃[ g ∶ Trackable Y X ] (∼-eq Y Y (f ∘ g) (id Y)) × (∼-eq X X (g ∘ f) (id X))
