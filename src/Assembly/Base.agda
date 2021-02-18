{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped
  hiding (Z)

record IsRealisability {X : 𝓤 ̇} (_⊩_ : Λ₀ → X → 𝓤 ̇) : 𝓤 ̇ where
  field
    ⊩-respects-↠  : _⊩_ respects _-↠_ on-the-left
    ⊩-right-total : IsRightTotal _⊩_ 

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    _⊩_             : Λ₀ → X → 𝓤 ̇
    -- TODO: Perhaps ⊩ should also be a mere proposition
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
-- Morphisms between assemblies

Tracks : (X Y : Asm 𝓤)
  → (F : ⋆ , ∅ ⊢ ⋆)
  → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →     M   X.⊩ x    
  → F [ M ] Y.⊩ (f x)
  -- TODO: Clarify if this needs to be ∥ ... ∥
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
id = 𝓤.id , 0 , 𝓤.id

infixr 9 _∘_

-- TODO: Clarify this definition. It seems that _∘_ preserves identities and is associative
-- with respect to three components.
_∘_ : Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {Z = Z} (g , G , G⊩g) (f , F , F⊩f) = g 𝓤.∘ f , (G ∘′ F) , λ {M} {x} M⊩x →
  subst (_⊩ g (f x)) (∘-ssubst-ssubst G F _ ⁻¹) (G⊩g (F⊩f M⊩x))
    where open AsmStr (str Z)

------------------------------------------------------------------------------
-- Examples

∇_ : (X : 𝓤 ̇) → Asm 𝓤
∇ X = X , (λ _ _ → Unit*) , record
  { ⊩-respects-↠  = λ _ _ → tt*
  ; ⊩-right-total = λ _ → ∣ 𝑰 , tt* ∣ }

⊩⊥ : Λ₀ → ⊥* {𝓤} → 𝓤 ̇
⊩⊥ _ ()

⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , ⊩⊥ , record
  { ⊩-respects-↠  = λ { {y = ()} }
  ; ⊩-right-total = λ ()
  }

⊤ₐ : Asm 𝓤
⊤ₐ = Unit* , (λ M _ → Lift (M -↠ 𝑰)) , record
  { ⊩-respects-↠  = λ { M-↠M′ (lift M′-↠ƛ0) → lift (-↠-trans M-↠M′ M′-↠ƛ0) }
  ; ⊩-right-total = λ _ → ∣ 𝑰 , lift -↠-refl ∣
  }

------------------------------------------------------------------------------
-- Universality

weak-finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
weak-finality X = (λ _ → tt*) , (↑₁ 𝑰) , λ _ → lift -↠-refl

initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality X = ⊥*-elim , 0 , (λ { {x = ()} })

_⊩ℕ_ : Λ₀ → ℕ → 𝓤₀ ̇
M ⊩ℕ n = M -↠ 𝒄 n

⊩ℕ-respect-↠ : _⊩ℕ_ respects _-↠_ on-the-left
⊩ℕ-respect-↠ = -↠-trans

⊩ℕ-right-total : IsRightTotal _⊩ℕ_
⊩ℕ-right-total n = ∣ 𝒄 n , -↠-refl ∣

ℕₐ : Asm₀
ℕₐ = ℕ , _⊩ℕ_ , record
  { ⊩-respects-↠  = ⊩ℕ-respect-↠
  ; ⊩-right-total = ⊩ℕ-right-total }
    
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_×ₐ_ {𝓤} X Y = ⟨ X ⟩ × ⟨ Y ⟩ , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respect-↠
  ; ⊩-right-total = ⊩-right-total }
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

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
projₗ X Y = (λ {(x , y) → x}) , 0 · ↑₁ 𝑻 , F⊩projₗ
  where
    module X = AsmStr (str X)
    F⊩projₗ : Tracks (X ×ₐ Y) X (0 · ↑₁ 𝑻) λ {(x , y) → x}
    F⊩projₗ (_ , _ , πₗL-↠M , M⊩x , _ , _) = X.⊩-respects-↠ πₗL-↠M M⊩x

projᵣ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) Y
projᵣ X Y = (λ {(x , y) → y}) , 0 · ↑₁ 𝑭 , F⊩projᵣ
  where
    module Y = AsmStr (str Y)
    F⊩projᵣ : Tracks (X ×ₐ Y) Y (0 · ↑₁ 𝑭) λ {(x , y) → y}
    F⊩projᵣ (_ , _ , _ , _ , π₂L-↠N , N⊩y) = Y.⊩-respects-↠ π₂L-↠N N⊩y

-- Exponential consists of trackable functions.
_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_⇒_ {𝓤} X Y = (Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥) , _⊩_ , record
  { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respects-↠ {x} {x′} {y}
  ; ⊩-right-total = ⊩-right-total }
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

      _⊩_ : Λ₀ → Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥ → 𝓤 ̇
      F ⊩ (f , _) = Tracks X Y (↑₁ F · 0) f 

      ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respects-↠ {G} {F} {f , _} G-↠F F⊩f {M} M⊩x = Y.⊩-respects-↠
        (subst-reduce* {M = (↑₁ G) · 0} {σ = subst-zero M} (·ₗ-cong (rename-reduce* G-↠F)))
        (F⊩f M⊩x) 

      ⊩-right-total : _
      ⊩-right-total (f , t) = rec propTruncIsProp
        (λ { (F , F⊩f) → ∣ ƛ F , (λ {M} {x} M⊩x → Y.⊩-respects-↠ (lem F M) (F⊩f M⊩x)) ∣}) t
        where
          open -↠-Reasoning
          lem : (F : ⋆ , ∅ ⊢ ⋆) → (M : Λ₀) → ((↑₁ (ƛ F)) · 0) [ M ] -↠ F [ M ]
          lem F M = begin
            ↑₁ (ƛ F) [ M ] · M
              ≡⟨ cong {B = λ _ → Λ₀} (_· M) (subst-rename-∅ (subst-zero M) (ƛ F)) ⟩
            (ƛ F) · M
              -→⟨ β ⟩
            F [ M ]
              ∎

postulate
  ev : (X Y : Asm 𝓤) → Trackable ((X ⇒ Y) ×ₐ X) Y
