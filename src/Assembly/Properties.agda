{-# OPTIONS --without-K --cubical #-}

module Assembly.Properties where

open import Prelude as 𝓤
  hiding (_∘_; id; uncurry)
open import Calculus.Untyped as Λ
  hiding (Z; `⟨_,_⟩)

open import Assembly.Base

private
  variable
    X Y Z : Asm 𝓤
    x y z : ⟨ X ⟩

∇_ : (X : 𝓤 ̇) → Asm 𝓤
∇ X = X , (λ _ _ → Unit*) , record
  { ⊩-respects-↠ = λ _ _ → tt*
  ; ⊩-right-total = λ _ → ∣ 𝑰 , tt* ∣
  ; ⊩-isProp     = λ _ _ → isPropUnit*
  }

ℕₐ : Asm₀
ℕₐ = ℕ , _⊩_ , record
  { ⊩-respects-↠  = λ M-↠N N⊩n → ∥-∥map (-↠-trans M-↠N) N⊩n
  ; ⊩-right-total = λ n → ∣ 𝒄 n , ∣ -↠-refl ∣ ∣
  ; ⊩-isProp      = λ _ _ → propTruncIsProp
  }
  where
    _⊩_ : Λ₀ → ℕ → 𝓤₀ ̇
    M ⊩ n = ∥ M -↠ 𝒄 n ∥

-- Proposition: The set Λ₀ of lambda terms is equipped with an assembly structure.
Λ₀ₐ : Asm 𝓤₀
Λ₀ₐ = Λ₀ , (λ M N → ∥ M -↠ N ∥) , record
  { ⊩-respects-↠  = λ r → ∥-∥map (-↠-trans r)
  ; ⊩-right-total = λ M → ∣ M , ∣ -↠-refl ∣ ∣
  ; ⊩-isProp      = λ M x → propTruncIsProp
  }

------------------------------------------------------------------------------
-- Finality
⊤ₐ : Asm 𝓤
⊤ₐ = Unit* , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respects-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isProp      = λ _ _ → propTruncIsProp
  }
  where
    _⊩_ : Λ₀ → Unit* {𝓤} → 𝓤 ̇
    M ⊩ _ = ∥ M -↠ 𝑰 ∥*

    ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
    ⊩-respects-↠ M-↠M′ M′-↠𝑰 = ∥-∥map (λ M′-↠𝑰 → lift (-↠-trans M-↠M′ (lower M′-↠𝑰))) M′-↠𝑰

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total _ = ∣ 𝑰 , ∣ -↠-refl ∣* ∣
    
module Final {X : Asm 𝓤} where
  open AsmStr (str X)
  open -↠-Reasoning

  universality : Trackable X ⊤ₐ
  universality = (λ _ → tt*) , (↑₁ 𝑰) , λ _ → ∣ -↠-refl ∣*

  global-element : (x : ⟨ X ⟩) → (M : Λ₀) → M ⊩ x
    → Trackable ⊤ₐ X
  global-element x M M⊩x = (λ _ → x) , (↑₁ M) , λ _ → ⊩-respects-↠ (↑₁ M [ _ ] ≡⟨ subst-rename-∅ _ M ⟩ M ∎ ) M⊩x

  separator : (f g : Trackable X Y)
    → isSet ⟨ Y ⟩
    → ((x : Trackable ⊤ₐ X) → f ∘ x ∼ g ∘ x ꞉ ⊤ₐ →ₐ Y)
    → f ∼ g ꞉ X →ₐ Y
  separator {Y = Y} f g YisSet fx=gx x = rec (YisSet _ _)
    (λ {(M , M⊩x) → fx=gx (global-element x M M⊩x) tt*}) (X.⊩-right-total x)
    where
      module Y = AsmStr (str Y)
      module X = AsmStr (str X)
      
*→Λ : (M : Λ₀) → Trackable ⊤ₐ Λ₀ₐ
*→Λ M = Final.global-element M M ∣ -↠-refl ∣

------------------------------------------------------------------------------
-- Initiality
⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respects-↠ 
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isProp      = λ _ ()
  }
  where
    _⊩_ : Λ₀ → ⊥* {𝓤} → 𝓤 ̇
    _ ⊩ ()

    ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
    ⊩-respects-↠ {y = ()}
 
    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total ()

module Initial (X : Asm 𝓤) where 
  universality : Trackable ⊥ₐ X
  universality = ⊥*-elim , 0 , (λ { {x = ()} })

  strict : (f : Trackable X ⊥ₐ) → AsmIso X ⊥ₐ f
  strict (f , F , F⊩f) = ∣ universality , (λ ()) , (λ x → ⊥*-elim (transport ⊥=X x)) ∣
    where
      ⊥=X : ⟨ X ⟩ ≡ ⊥*
      ⊥=X = ua (strict-initial f)
    
------------------------------------------------------------------------------
-- Product
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_×ₐ_ {𝓤} X Y = ⟨ X ⟩ × ⟨ Y ⟩ , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respect-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isProp      = λ _ _ → isProp× propTruncIsProp propTruncIsProp }
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    _⊩_ : Λ₀ → ⟨ X ⟩ × ⟨ Y ⟩ → 𝓤 ̇
    L ⊩ (x , y) =
      ∥ Σ[ M ꞉ Λ₀ ] `projₗ L -↠ M × M X.⊩ x ∥ ×
      ∥ Σ[ N ꞉ Λ₀ ] `projᵣ L -↠ N × N Y.⊩ y ∥

    ⊩-respect-↠   : _⊩_ respects _-↠_ on-the-left
    ⊩-respect-↠ L-↠L′ (r , s) =
      ∥-∥map (λ { (M , L₁-↠M , r′) → M , -↠-trans (·ₗ-cong L-↠L′) L₁-↠M , r′ }) r ,
      ∥-∥map (λ { (N , L₂-↠N , s′) → N , -↠-trans (·ₗ-cong L-↠L′) L₂-↠N , s′ }) s 

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total (x , y) = rec2 propTruncIsProp
      (λ { (M , M⊩x) (N , N⊩y) → ∣ Λ.`⟨ M , N ⟩ , ∣ M , β-projₗ , M⊩x ∣ , ∣ N , β-projᵣ , N⊩y ∣ ∣ })
      (X.⊩-right-total x) (Y.⊩-right-total y)

module Product (X Y : Asm 𝓤) where
  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  X×Y = X ×ₐ Y
  module X×Y = AsmStr (str X×Y)
  
  
  projₗ : Trackable X×Y X
  projₗ = (λ {(x , y) → x}) , 0 · ↑₁ 𝑻 , F⊩projₗ
    where
      F⊩projₗ : Tracks X×Y X (0 · ↑₁ 𝑻) fst
      F⊩projₗ {M} {x} (M⊩x , _) = rec (X.⊩-isProp _ _) (λ { (_ , πₗL-↠M , M⊩x) → X.⊩-respects-↠ πₗL-↠M M⊩x }) M⊩x

--   projᵣ : Trackable X×Y Y
--   projᵣ = (λ {(x , y) → y}) , 0 · ↑₁ 𝑭 , F⊩projᵣ
--     where
--       F⊩projᵣ : Tracks X×Y Y (0 · ↑₁ 𝑭) snd
--       F⊩projᵣ (_ , _ , _ , _ , π₂L-↠N , N⫣y) = Y.⊩-respects-↠ π₂L-↠N N⫣y
      
--   `⟨_,_⟩ : {Z : Asm 𝓤}
--     → Trackable Z X → Trackable Z Y → Trackable Z (X ×ₐ Y)
--   `⟨_,_⟩ {Z = Z} (f , F , F⊩f) (g , G , G⊩g) = h , H , H⊩h 
--     where
--       module Z   = AsmStr (str Z)
--       open -↠-Reasoning

--       h : _ → ⟨ X×Y ⟩
--       h z = f z , g z

--       H = Λ.`⟨ F , G ⟩

--       H⊩h : Tracks Z (X ×ₐ Y) H h
--       H⊩h {L} {z} L⊩z = F [ L ] , lem₁ , F⊩f L⊩z , G [ L ] , lem₂ , G⊩g L⊩z
--         where
--           lem₁ = begin
--             `projₗ (H [ L ])
--               ≡⟨ refl ⟩
--             (ƛ 0 · ↑₁ F ⟪ exts (subst-zero L) ⟫ · ↑₁ G ⟪ exts (subst-zero L) ⟫) · 𝑻
--               ≡⟨ cong₂ (λ M N → (ƛ 0 · M · N) · 𝑻) (rename-exts (subst-zero L) F) (rename-exts (subst-zero L) G) ⟩
--             (ƛ 0 · ↑₁ (F [ L ]) · ↑₁ (G [ L ])) · 𝑻
--               -↠⟨ β-projₗ ⟩
--             F [ L ] ∎

--           lem₂ = begin
--             `projᵣ (H [ L ])
--               ≡⟨ refl ⟩
--             (ƛ 0 · ↑₁ F ⟪ exts (subst-zero L) ⟫ · ↑₁ G ⟪ exts (subst-zero L) ⟫) · 𝑭
--               ≡⟨ cong₂ (λ M N → (ƛ 0 · M · N) · 𝑭) (rename-exts (subst-zero L) F) (rename-exts (subst-zero L) G) ⟩
--             (ƛ 0 · ↑₁ (F [ L ]) · ↑₁ (G [ L ])) · 𝑭
--               -↠⟨ β-projᵣ ⟩
--             G [ L ] ∎
-- ------------------------------------------------------------------------------
-- -- Exponential object
-- infixr 15 _⇒_

-- _⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
-- _⇒_ {𝓤} X Y = X⇒Y , _⊩_ , record
--   { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respects-↠ {x} {x′} {y}
--   ; ⊩-right-total = ⊩-right-total }
--     where
--       open -↠-Reasoning
--       module X = AsmStr (str X)
--       module Y = AsmStr (str Y)

--       X⇒Y = MerelyTrackable X Y

--       _⊩_ : Λ₀ → X⇒Y → 𝓤 ̇
--       F ⊩ (f , _) = {M : Λ₀} {x : ⟨ X ⟩} → M X.⊩ x → F · M Y.⊩ f x

--       ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
--       ⊩-respects-↠ {G} {F} G-↠F F⊩f M⊩x = Y.⊩-respects-↠ (·ₗ-cong G-↠F) (F⊩f M⊩x)

--       ⊩-right-total : _⊩_ IsRightTotal
--       ⊩-right-total (f , ∃F⊩f) = rec propTruncIsProp
--         (λ { (F , F⊩f) → ∣ ƛ F , (λ {M} {x} M⊩x → Y.⊩-respects-↠
--           ((ƛ F) · M -→⟨ β ⟩ F [ M ] ∎) (F⊩f M⊩x)) ∣})
--         ∃F⊩f
        
-- module Exponential (X Y : Asm 𝓤) where
--   module X = AsmStr (str X)
--   module Y = AsmStr (str Y)
--   X⇒Y = X ⇒ Y
--   module X⇒Y = AsmStr (str X⇒Y)
--   open -↠-Reasoning
      
--   postulate
--     uncurry : {Z : Asm 𝓤} → Trackable (Z ×ₐ X) Y → Trackable Z X⇒Y
--     eval : Trackable (X⇒Y ×ₐ X) Y
--     {-
--       uncurry {Z = Z} (f , F , F⊩f) = (λ z → (λ x → f (z , x)) , rec propTruncIsProp
--         (λ { (L , L⊩z) → ∣ ↑₁ (ƛ F) · Λ.`⟨ ↑₁ L , 0 ⟩ , {!!} ∣ }) (Z.⊩-right-total z)) , 
--         {!!} , {!!}
--         where
--           module Z = AsmStr (str Z)
--       -}
