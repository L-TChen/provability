{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped
  hiding (Z)

record IsRealisability {X : 𝓤 ̇} (_⫣_ : X → Λ₀ → 𝓤 ̇) : 𝓤 ̇ where
  field
    ⫣-respects-↠ : _⫣_ respects _-↠_ on-the-right
    ⫣-left-total : _⫣_ IsLeftTotal 
--    ⫣-isProp     : (x : X) → (M : Λ₀) → isProp (x ⫣ M) 
    -- ⫣-isProp is usefu when defining □

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    _⫣_            : X → Λ₀ → 𝓤 ̇
    isRealisability : IsRealisability _⫣_
  open IsRealisability isRealisability public
  infix 6 _⫣_

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
  → Λ₁
  → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →   x X.⫣ M    
  → f x Y.⫣ F [ M ]
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
    F⫣f : Tracks X Y F f

Trackable : (X Y : Asm 𝓤) → 𝓤 ̇
Trackable X Y = Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] HasTracker X Y f
 
∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , _) (g , _) = (x : ⟨ X ⟩) → f x ≡ g x

infix 4 ∼-syntax

syntax ∼-syntax {X = X} {Y = Y} f g = f ∼ g ꞉ X →ₐ Y

∼-syntax : {X Y : Asm 𝓤} → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

id : Trackable X X
id = 𝓤.id , 0 , 𝓤.id

infixr 9 _∘_

-- TODO: Clarify this definition.
_∘_ : Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {Z = Z} (g , G , g⫣G) (f , F , f⫣F) = g 𝓤.∘ f , (G ∘′ F) , λ {_} {x} x⫣M →
  subst (g (f x) ⫣_) (∘-ssubst-ssubst G F _ ⁻¹) (g⫣G (f⫣F x⫣M))
    where open AsmStr (str Z)

∘-commutes-𝓤∘ : (g : Trackable Y Z) (f : Trackable X Y) → (x : ⟨ X ⟩) → (g ∘ f) .fst x ≡ g .fst (f .fst x)
∘-commutes-𝓤∘ g f x = refl
------------------------------------------------------------------------------
-- Examples

∇_ : (X : 𝓤 ̇) → Asm 𝓤
∇ X = X , (λ _ _ → Unit*) , record
  { ⫣-respects-↠ = λ _ _ → tt*
  ; ⫣-left-total = λ _ → ∣ 𝑰 , tt* ∣
--  ; ⫣-isProp     = λ _ _ → isPropUnit*
  }

⫣⊥ : ⊥* {𝓤} → Λ₀ → 𝓤 ̇
⫣⊥ ()

⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , ⫣⊥ , record
  { ⫣-respects-↠ = λ { {x = ()} }
  ; ⫣-left-total = λ ()
--  ; ⫣-isProp     = λ ()
  }

⊤ₐ : Asm 𝓤
⊤ₐ = Unit* , (λ _ M → ∥ Lift (M -↠ 𝑰) ∥) , record
  { ⫣-respects-↠ = λ { M-↠M′ M′-↠ƛ0 → rec propTruncIsProp (λ { (lift r) → ∣ lift (-↠-trans M-↠M′ r) ∣ }) M′-↠ƛ0 } 
  ; ⫣-left-total = λ _ → ∣ 𝑰 , ∣ lift -↠-refl ∣ ∣
  -- ; ⫣-isProp     = λ _ _ → propTruncIsProp 
  }

------------------------------------------------------------------------------
-- Universality

weak-finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
weak-finality X = (λ _ → tt*) , (↑₁ 𝑰) , λ _ → ∣ lift -↠-refl ∣

initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality X = ⊥*-elim , 0 , (λ { {x = ()} })

_⫣ℕ_ : ℕ → Λ₀ → 𝓤₀ ̇
n ⫣ℕ M = M -↠ 𝒄 n

⫣ℕ-respect-↠ : _⫣ℕ_ respects _-↠_ on-the-right
⫣ℕ-respect-↠ = -↠-trans

⫣ℕ-left-total : _⫣ℕ_ IsLeftTotal 
⫣ℕ-left-total n = ∣ 𝒄 n , -↠-refl ∣

ℕₐ : Asm₀
ℕₐ = ℕ , _⫣ℕ_ , record
  { ⫣-respects-↠ = ⫣ℕ-respect-↠
  ; ⫣-left-total = ⫣ℕ-left-total }
    
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_×ₐ_ {𝓤} X Y = ⟨ X ⟩ × ⟨ Y ⟩ , _⫣_ , record
  { ⫣-respects-↠  = ⫣-respect-↠
  ; ⫣-left-total = ⫣-left-total }
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    _⫣_ : ⟨ X ⟩ × ⟨ Y ⟩ → Λ₀ → 𝓤 ̇
    (x , y) ⫣ L = Σ[ M ꞉ Λ₀ ] Σ[ N ꞉ Λ₀ ] `projₗ L -↠ M × x X.⫣ M × `projᵣ L -↠ N × y Y.⫣ N

    ⫣-respect-↠   : _⫣_ respects _-↠_ on-the-right
    ⫣-respect-↠ {x = x , y} L-↠L′ (M , N , proj₁L-↠M , M⫣x , projᵣL-↠N , N⫣y) =
      M , N , -↠-trans (·ₗ-cong L-↠L′) proj₁L-↠M , M⫣x , -↠-trans (·ₗ-cong L-↠L′) projᵣL-↠N , N⫣y

    ⫣-left-total : _⫣_ IsLeftTotal
    ⫣-left-total (x , y) = rec propTruncIsProp
      (λ {(M , M⫣x) → rec propTruncIsProp
      (λ {(N , N⫣y) → ∣ `⟨ M , N ⟩ , M , N , β-projₗ , M⫣x , β-projᵣ , N⫣y ∣})
      (Y.⫣-left-total y)}) (X.⫣-left-total x)

projₗ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) X
projₗ X Y = (λ {(x , y) → x}) , 0 · ↑₁ 𝑻 , F⫣projₗ
  where
    module X = AsmStr (str X)
    F⫣projₗ : Tracks (X ×ₐ Y) X (0 · ↑₁ 𝑻) λ {(x , y) → x}
    F⫣projₗ (_ , _ , πₗL-↠M , M⫣x , _ , _) = X.⫣-respects-↠ πₗL-↠M M⫣x

projᵣ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) Y
projᵣ X Y = (λ {(x , y) → y}) , 0 · ↑₁ 𝑭 , F⫣projᵣ
  where
    module Y = AsmStr (str Y)
    F⫣projᵣ : Tracks (X ×ₐ Y) Y (0 · ↑₁ 𝑭) λ {(x , y) → y}
    F⫣projᵣ (_ , _ , _ , _ , π₂L-↠N , N⫣y) = Y.⫣-respects-↠ π₂L-↠N N⫣y

-- Exponential consists of trackable functions.
_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_⇒_ {𝓤} X Y = (Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥) , _⫣_ , record
  { ⫣-respects-↠ = λ {x} {x′} {y} → ⫣-respects-↠ {x} {x′} {y}
  ; ⫣-left-total = ⫣-left-total }
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

      _⫣_ : Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥ → Λ₀ → 𝓤 ̇
      (f , _) ⫣ F = Tracks X Y (↑₁ F · 0) f 

      ⫣-respects-↠ : _⫣_ respects _-↠_ on-the-right
      ⫣-respects-↠ {G} {F} {f , _} G-↠F F⫣f {M} M⫣x = Y.⫣-respects-↠
        (subst-reduce* {M = (↑₁ G) · 0} {σ = subst-zero M} (·ₗ-cong (rename-reduce* G-↠F)))
        (F⫣f M⫣x) 

      ⫣-left-total : _
      ⫣-left-total (f , t) = rec propTruncIsProp
        (λ { (F , F⫣f) → ∣ ƛ F , (λ {M} {x} M⫣x → Y.⫣-respects-↠ (lem F M) (F⫣f M⫣x)) ∣}) t
        where
          open -↠-Reasoning
          lem : (F : Λ₁) → (M : Λ₀) → (↑₁ (ƛ F) · 0) [ M ] -↠ F [ M ]
          lem F M = begin
            ↑₁ (ƛ F) [ M ] · M
              ≡⟨ cong {B = λ _ → Λ₀} (_· M) (subst-rename-∅ (subst-zero M) (ƛ F)) ⟩
            (ƛ F) · M
              -→⟨ β ⟩
            F [ M ]
              ∎

postulate
  ev : (X Y : Asm 𝓤) → Trackable ((X ⇒ Y) ×ₐ X) Y
