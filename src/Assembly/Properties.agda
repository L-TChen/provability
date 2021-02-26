{-# OPTIONS --without-K --cubical #-}

module Assembly.Properties where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.Untyped
  hiding (Z)

open import Assembly.Base

private
  variable
    X Y Z : Asm 𝓤
    x y z : ⟨ X ⟩

∇_ : (X : 𝓤 ̇) → Asm 𝓤
∇ X = X , (λ _ _ → Unit*) , record
  { ⊩-respects-↠ = λ _ _ → tt*
  ; ⊩-right-total = λ _ → ∣ 𝑰 , tt* ∣
--  ; ⫣-isProp     = λ _ _ → isPropUnit*
  }

ℕₐ : Asm₀
ℕₐ = ℕ , _⊩_ , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ n → ∣ 𝒄 n , -↠-refl ∣ }
  where
    _⊩_ : Λ₀ → ℕ → 𝓤₀ ̇
    M ⊩ n = M -↠ 𝒄 n

-- Proposition: The set Λ₀ of lambda terms is equipped with an assembly structure.
Λ₀ₐ : Asm 𝓤₀
Λ₀ₐ = Λ₀ , (λ M N → M -↠ N) , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ M → ∣ M , -↠-refl ∣
  }

------------------------------------------------------------------------------
-- Finality
⊤ₐ : Asm 𝓤
⊤ₐ = Unit* , (λ M _ → ∥ Lift (M -↠ 𝑰) ∥) , record
  { ⊩-respects-↠  = λ { M-↠M′ M′-↠ƛ0 → rec propTruncIsProp (λ { (lift r) → ∣ lift (-↠-trans M-↠M′ r) ∣ }) M′-↠ƛ0 } 
  ; ⊩-right-total = λ _ → ∣ 𝑰 , ∣ lift -↠-refl ∣ ∣
  -- ; ⫣-isProp     = λ _ _ → propTruncIsProp 
  }
finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
finality X = (λ _ → tt*) , (↑₁ 𝑰) , λ _ → ∣ lift -↠-refl ∣

------------------------------------------------------------------------------
-- Initiality
⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , ⊩⊥ , record
  { ⊩-respects-↠  = λ { {y = ()} }
  ; ⊩-right-total = λ ()
--  ; ⫣-isProp     = λ ()
  }
  where
    ⊩⊥ : Λ₀ → ⊥* {𝓤} → 𝓤 ̇
    ⊩⊥ _ ()

initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality X = ⊥*-elim , 0 , (λ { {x = ()} })

global-element : (X : Asm 𝓤) → (x : ⟨ X ⟩) → (M : Λ₀) → (AsmStr._⊩_ (str X) M x)
  → Trackable ⊤ₐ X
global-element X x M M⊩x = (λ _ → x) , (↑₁ M) , λ _ → ⊩-respects-↠ (↑₁ M [ _ ] ≡⟨ subst-rename-∅ _ M ⟩ M ∎ ) M⊩x
  where
    open AsmStr (str X)
    open -↠-Reasoning

*→Λ : (M : Λ₀) → Trackable ⊤ₐ Λ₀ₐ
*→Λ M = global-element Λ₀ₐ M M -↠-refl
    
------------------------------------------------------------------------------
-- Product
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_×ₐ_ {𝓤} X Y = ⟨ X ⟩ × ⟨ Y ⟩ , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respect-↠
  ; ⊩-right-total = ⊩-right-total  }
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    _⊩_ : Λ₀ → ⟨ X ⟩ × ⟨ Y ⟩ → 𝓤 ̇
    L ⊩ (x , y) = Σ[ M ꞉ Λ₀ ] Σ[ N ꞉ Λ₀ ] `projₗ L -↠ M × M X.⊩ x × `projᵣ L -↠ N × N Y.⊩ y

    ⊩-respect-↠   : _⊩_ respects _-↠_ on-the-left
    ⊩-respect-↠ L-↠L′ (M , N , proj₁L-↠M , x⊩M , projᵣL-↠N , y⊩N) =
      M , N , -↠-trans (·ₗ-cong L-↠L′) proj₁L-↠M , x⊩M , -↠-trans (·ₗ-cong L-↠L′) projᵣL-↠N , y⊩N

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total (x , y) = rec propTruncIsProp
      (λ {(M , M⫣x) → rec propTruncIsProp
      (λ {(N , N⫣y) → ∣ `⟨ M , N ⟩ , M , N , β-projₗ , M⫣x , β-projᵣ , N⫣y ∣})
      (Y.⊩-right-total y)}) (X.⊩-right-total x)

projₗ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) X
projₗ X Y = (λ {(x , y) → x}) , 0 · ↑₁ 𝑻 , F⫣projₗ
  where
    module X = AsmStr (str X)
    F⫣projₗ : Tracks (X ×ₐ Y) X (0 · ↑₁ 𝑻) fst 
    F⫣projₗ (_ , _ , πₗL-↠M , M⫣x , _ , _) = X.⊩-respects-↠ πₗL-↠M M⫣x

projᵣ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) Y
projᵣ X Y = (λ {(x , y) → y}) , 0 · ↑₁ 𝑭 , F⫣projᵣ
  where
    module Y = AsmStr (str Y)
    F⫣projᵣ : Tracks (X ×ₐ Y) Y (0 · ↑₁ 𝑭) snd
    F⫣projᵣ (_ , _ , _ , _ , π₂L-↠N , N⫣y) = Y.⊩-respects-↠ π₂L-↠N N⫣y

-- Exponential consists of trackable functions.
infixr 15 _⇒_

_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_⇒_ {𝓤} X Y = (Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∃[ F ꞉ Λ₁ ] Tracks X Y F f) , _⊩_ , record
  { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respects-↠ {x} {x′} {y}
  ; ⊩-right-total = ⊩-right-total }
    where
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

      _⊩_ : Λ₀ → Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] (∃[ F ꞉ Λ₁ ] Tracks X Y F f) → 𝓤 ̇
      F ⊩ (f , _) = Tracks X Y (↑₁ F · 0) f

      ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respects-↠ {G} {F} G-↠F F⫣f M⫣x = Y.⊩-respects-↠
        (subst-reduce* {M = ↑₁ G · 0} (·ₗ-cong (rename-reduce* G-↠F)))
        (F⫣f M⫣x) 

      ⊩-right-total : _⊩_ IsRightTotal
      ⊩-right-total (f , ∃F⊩f) = rec propTruncIsProp
        (λ { (F , F⊩f) → ∣ ƛ F , (λ {M} {x} M⊩x → Y.⊩-respects-↠ (lem F M) (F⊩f M⊩x)) ∣ }) ∃F⊩f
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

{-
ev : (X Y : Asm 𝓤) → Trackable ((X ⇒ Y) ×ₐ X) Y
ev X Y = {!!}
-}
