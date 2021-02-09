{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped
  hiding (Z)

record IsRealisability {X : 𝓤 ̇} (_⊩_ : Λ₀ → X → 𝓤 ̇) : 𝓤 ̇ where
  constructor is⊩
  field
    ⊩-respects-↠   : _⊩_ respects _-↠_ on-the-left
    ⊩-right-total : IsRightTotal _⊩_ 

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

private
  variable
    X Y Z : Asm 𝓤
    x y z : ⟨ X ⟩

------------------------------------------------------------------------------
-- Examples
∇_ : (X : 𝓤 ̇) → Asm 𝓤
∇ X = X , (λ _ _ → Unit*) , is⊩ (λ _ _ → tt*)
  λ _  → ∣ 𝑰 , tt* ∣

⊩⊥ : Λ₀ → ⊥* {𝓤} → 𝓤 ̇
⊩⊥ _ ()

⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , ⊩⊥ , is⊩ (λ { {y = ()} }) λ ()

⊤ₐ : Asm 𝓤
⊤ₐ = ∇ Unit* 

------------------------------------------------------------------------------
-- Morphisms between assemblies

Tracks : (X Y : Asm 𝓤)
  → (F : ⋆ , ∅ ⊢ ⋆)
  → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →     M   X.⊩ x    
  → F [ M ] Y.⊩ (f x)
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor _,_

  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  field
    F   : ⋆ , ∅ ⊢ ⋆
    F⊩f : Tracks X Y F f

record Trackable (X Y : Asm 𝓤) : 𝓤 ̇ where
  constructor _,_
  field
    fun        : ⟨ X ⟩ → ⟨ Y ⟩
    hasTracker : HasTracker X Y fun
  open HasTracker hasTracker public
 
∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , _) (g , _) = f ≡ g

infix 4 ∼-syntax

syntax ∼-syntax {X = X} {Y = Y} f g = f ∼ g ꞉ X →ₐ Y

∼-syntax : {X Y : Asm 𝓤} → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

id : Trackable X X
id = (λ x → x) , 0 , λ M⊩x → M⊩x

infixr 9 _∘_

_∘_ : {X Y Z : Asm 𝓤} → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {𝓤} {X} {Y} {Z} (g , G , G⊩g) (f , F , F⊩f) = g 𝓤.∘ f , {!!} , λ {M} {x} M⊩x → {!G⊩g !}

-- ------------------------------------------------------------------------------
-- Universality

-- Uniqueness up to ∼ follows from function extensionality.
finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
finality (|X| , ⊩ , _isRealisable) = (λ _ → tt*) , 0 , λ x → tt* 

-- Uniqueness up to ∼ follows from function extensionality.
initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality {𝓤} X@(|X| , _⊩_ , _isRealisable) = ⊥*-elim , 0 , (λ { {x = ()} })

_⊩ℕ_ : Λ₀ → ℕ → 𝓤₀ ̇
M ⊩ℕ n = M -↠ 𝒄 n

⊩ℕ-respect-↠ : _⊩ℕ_ respects _-↠_ on-the-left
⊩ℕ-respect-↠ = -↠-trans

⊩ℕ-right-total : IsRightTotal _⊩ℕ_
⊩ℕ-right-total n = ∣ 𝒄 n , -↠-refl ∣

ℕₐ : Asm₀
ℕₐ = ℕ , _⊩ℕ_ , is⊩ ⊩ℕ-respect-↠ ⊩ℕ-right-total
    
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_×ₐ_ {𝓤} X Y = ⟨ X ⟩ × ⟨ Y ⟩ , _⊩_ , is⊩ ⊩-respect-↠ ⊩-right-total
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    open -↠-Reasoning

    _⊩_ : Λ₀ → ⟨ X ⟩ × ⟨ Y ⟩ → 𝓤 ̇
    L ⊩ (x , y) = Σ[ M ꞉ Λ₀ ] Σ[ N ꞉ Λ₀ ] `projₗ L -↠ M × M X.⊩ x × `projᵣ L -↠ N × N Y.⊩ y

    ⊩-respect-↠   : _⊩_ respects _-↠_ on-the-left
    ⊩-respect-↠ {y = x , y} L-↠L′ (M , N , proj₁L-↠M , M⊩x , projᵣL-↠N , N⊩y) =
      M , N , -↠-trans (·ₗ-cong L-↠L′) proj₁L-↠M , M⊩x , -↠-trans (·ₗ-cong L-↠L′) projᵣL-↠N , N⊩y

    ⊩-right-total : IsRightTotal _⊩_
    ⊩-right-total (x , y) = rec propTruncIsProp
      (λ {(M , M⊩x) → rec propTruncIsProp
      (λ {(N , N⊩y) → ∣ `⟨ M , N ⟩ , M , N , β-projₗ , M⊩x , β-projᵣ , N⊩y ∣})
      (Y.⊩-right-total y)}) (X.⊩-right-total x)

projₗ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) X
projₗ X Y = (λ {(x , y) → x}) , 0 · ↑ 𝑻 , F⊩projₗ
  where
    module X = AsmStr (str X)
    F⊩projₗ : Tracks (X ×ₐ Y) X (0 · ↑ 𝑻) λ {(x , y) → x}
    F⊩projₗ (_ , _ , π₁L-↠M , M⊩x , _ , _) = X.⊩-respects-↠ π₁L-↠M M⊩x

projᵣ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) Y
projᵣ X Y = (λ {(x , y) → y}) , 0 · ↑ 𝑭 , F⊩projᵣ
  where
    module Y = AsmStr (str Y)
    F⊩projᵣ : Tracks (X ×ₐ Y) Y (0 · ↑ 𝑭) λ {(x , y) → y}
    F⊩projᵣ (_ , _ , _ , _ , π₂L-↠N , N⊩y) = Y.⊩-respects-↠ π₂L-↠N N⊩y

-- Exponentia consists of trackable functions.
_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_⇒_ {𝓤} X Y = (Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥) , _⊩_ ,
  is⊩ (λ {x} {x′} {y} → ⊩-respects-↠ {x} {x′} {y}) ⊩-right-total
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

      _⊩_ : Λ₀ → Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥ → 𝓤 ̇
      F ⊩ (f , _) = Tracks X Y (↑ F · 0) f 

      ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respects-↠ {G} {F} {f , _} G-↠F F⊩f {M} M⊩x = Y.⊩-respects-↠
        (begin
          (↑ G · 0) [ M ]
            -↠⟨ {!G-↠F!} ⟩
          (↑ F · 0) [ M ] ∎)
        (F⊩f M⊩x) 

      ⊩-right-total : _
      ⊩-right-total (f , t) = rec propTruncIsProp
        (λ { (F , F⊩f) → ∣ ƛ F , (λ {M} {x} M⊩x → Y.⊩-respects-↠ {!!} (F⊩f M⊩x)) ∣}) t

ev : (X Y : Asm 𝓤) → Trackable ((X ⇒ Y) ×ₐ X) Y
ev X Y = {!!}
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

