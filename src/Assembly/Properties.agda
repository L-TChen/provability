{-# OPTIONS --without-K --cubical #-}

module Assembly.Properties where

open import Prelude as 𝓤
  hiding (_∘_; id; uncurry)
open import Calculus.Untyped as Λ
  hiding (`⟨_,_⟩)

open import Assembly.Base

private
  variable
    X Y Z : Asm 𝓤

∘-id : {f : Trackable X Y} → f ∘ (id X) ≡ f
∘-id {X = X} {Y} {f , F , F⊩f} i = (λ x → f x) , Fx=F i , λ {M} {x} r → lem {M} {x} r i
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    Fx=F : (F ∘′ 0) ≡ F 
    Fx=F = ∘′-id-right F

    postulate
      lem : {M : Λ₀} {x : ⟨ X ⟩} (r : M X.⊩ x)
        → PathP (λ i → Fx=F i [ M ] Y.⊩ f x) (subst (Y._⊩ (f x)) (∘-ssubst-ssubst F 0 M ⁻¹) (F⊩f r)) (F⊩f r) 

id-∘ : {f : Trackable X Y} → id Y ∘ f ≡ f
id-∘ {X = X} {Y} {f , F , F⊩f} i = (λ x → f x) , F , λ {M} {x} r → lem {M} {x} r i
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    xF=F : 0 ∘′ F ≡ F
    xF=F = refl

    postulate
      lem : {M : Λ₀} {x : ⟨ X ⟩} (r : M X.⊩ x)
        → Path (F [ M ] Y.⊩ f x) (subst (Y._⊩ (f x)) (∘-ssubst-ssubst 0 F M ⁻¹) (F⊩f r)) (F⊩f r) 

{-
∘-ass : {A : ASM (universe-of ⟨ X ⟩)} {f : Trackable X Y} {g : Trackable Y Z} {h : Trackable Z A}
  → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-ass {X = X} {Y = Y} {Z = Z} {A = A} {f = f , F , F⊩f} {g , G , G⊩g} {h , H , H⊩h} i = (λ x → h (g (f x))) , ∘′-assoc H G F i ,
  λ r → lem r i
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    module Z = AsmStr (str Z)
    module A = AsmStr (str A)
    lem : {M : Λ₀} {x : ⟨ X ⟩} (r : M X.⊩ x)
      → PathP (λ i → ∘′-assoc H G F i [ M ] A.⊩ h (g (f x))) {!!} {!!} -- (H⊩h (G⊩g (F⊩f r)))
    lem = {!!}
-}

∇_ : (X : hSet 𝓤) → Asm 𝓤
∇ X = X , (λ _ _ → Unit*) , record
  { ⊩-respects-↠  = λ _ _ → tt*
  ; ⊩-right-total = λ _ → ∣ 𝑰 , tt* ∣
  ; ⊩-isSet       = isProp→isSet isPropUnit*
  }

ℕₐ : Asm₀
ℕₐ = (ℕ , isSetℕ) , _⊩_ , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ n → ∣ 𝒄 n , -↠-refl ∣
  ; ⊩-isSet       = -↠isSet 
  }
  where
    _⊩_ : Λ₀ → ℕ → 𝓤₀ ̇
    M ⊩ n = M -↠ 𝒄 n

-- Proposition: The set Λ₀ of lambda terms is equipped with an assembly structure.
Λ₀ₐ : Asm 𝓤₀
Λ₀ₐ = (Λ₀ , ≟→isSet) , (λ M N → M -↠ N) , record
  { ⊩-respects-↠  = -↠-trans
  ; ⊩-right-total = λ M → ∣ M , -↠-refl ∣
  ; ⊩-isSet       = -↠isSet 
  }

------------------------------------------------------------------------------
-- Finality
⊤ₐ : Asm 𝓤
⊤ₐ = (Unit* , isProp→isSet isPropUnit*) , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respects-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = isOfHLevelLift 2 -↠isSet 
  }
  where
    _⊩_ : Λ₀ → Unit* {𝓤} → 𝓤 ̇
    M ⊩ _ = Lift (M -↠ 𝑰)

    ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
    ⊩-respects-↠ M-↠M′ (lift M′-↠𝑰) = lift (-↠-trans M-↠M′ M′-↠𝑰)

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total _ = ∣ 𝑰 , lift -↠-refl ∣
    
module Final {X : Asm 𝓤} where
  open AsmStr (str X)
  open -↠-Reasoning

  universality : Trackable X ⊤ₐ
  universality = (λ _ → tt*) , (↑₁ 𝑰) , λ _ → lift -↠-refl

  global-element : (M : Λ₀) → (x : ⟨ X ⟩) → M ⊩ x
    → Trackable ⊤ₐ X
  global-element M x M⊩x = (λ _ → x) , (↑₁ M) , λ _ → ⊩-respects-↠ (↑₁ M [ _ ] ≡⟨ subst-rename-∅ _ M ⟩ M ∎ ) M⊩x

  separator : (f g : Trackable X Y)
    → ((x : Trackable ⊤ₐ X) → f ∘ x ∼ g ∘ x)
    → f ∼ g
  separator {Y = Y} f g fx=gx x = rec
    ((Y is-set) (⟨ f ⟩ x) (⟨ g ⟩ x)) (λ { (M , r) → fx=gx (global-element M x r) _ })
    (X.⊩-right-total x)
    where
      module Y = AsmStr (str Y)
      module X = AsmStr (str X)
      
*→Λ : (M : Λ₀) → Trackable ⊤ₐ Λ₀ₐ
*→Λ M = Final.global-element M M -↠-refl

------------------------------------------------------------------------------
-- Initiality
⊥ₐ : Asm 𝓤
⊥ₐ = (⊥* , λ ()) , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respects-↠ 
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = λ { {_} {()} } 
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
_×ₐ_ {𝓤} X Y = (⟨ X ⟩ × ⟨ Y ⟩ , isSet× (X is-set) (Y is-set) ) , _⊩_ , record
  { ⊩-respects-↠  = ⊩-respect-↠
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = isSet×
    (isSetΣ ≟→isSet λ _ → isSet× -↠isSet X.⊩-isSet)
    (isSetΣ ≟→isSet λ _ → isSet× -↠isSet Y.⊩-isSet)
  }
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    _⊩_ : Λ₀ → ⟨ X ⟩ × ⟨ Y ⟩ → 𝓤 ̇
    L ⊩ (x , y) =
      (Σ[ M ꞉ Λ₀ ] `projₗ L -↠ M × M X.⊩ x) ×
      (Σ[ N ꞉ Λ₀ ] `projᵣ L -↠ N × N Y.⊩ y)

    ⊩-respect-↠   : _⊩_ respects _-↠_ on-the-left
    ⊩-respect-↠ L-↠L′ ((M , proj₁L-↠M , x⊩M) , (N , projᵣL-↠N , y⊩N)) =
      (M , -↠-trans (·ₗ-cong L-↠L′) proj₁L-↠M , x⊩M) ,
      (N , -↠-trans (·ₗ-cong L-↠L′) projᵣL-↠N , y⊩N)

    ⊩-right-total : _⊩_ IsRightTotal
    ⊩-right-total (x , y) = rec2 propTruncIsProp
      (λ { (M , M⊩x) (N , N⊩y) → ∣ Λ.`⟨ M , N ⟩ , (M , β-projₗ , M⊩x) , N , β-projᵣ , N⊩y ∣ })
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
      F⊩projₗ ((_ , πₗL-↠M , M⫣x) , _) = X.⊩-respects-↠ πₗL-↠M M⫣x

  projᵣ : Trackable X×Y Y
  projᵣ = (λ {(x , y) → y}) , 0 · ↑₁ 𝑭 , F⊩projᵣ
    where
      F⊩projᵣ : Tracks X×Y Y (0 · ↑₁ 𝑭) snd
      F⊩projᵣ (_ , _ , π₂L-↠N , N⫣y) = Y.⊩-respects-↠ π₂L-↠N N⫣y
      
  `⟨_,_⟩ : {Z : Asm 𝓤}
    → Trackable Z X → Trackable Z Y → Trackable Z (X ×ₐ Y)
  `⟨_,_⟩ {Z = Z} (f , F , F⊩f) (g , G , G⊩g) = h , H , H⊩h 
    where
      module Z   = AsmStr (str Z)
      open -↠-Reasoning

      h : _ → ⟨ X×Y ⟩
      h z = f z , g z

      H = Λ.`⟨ F , G ⟩

      H⊩h : Tracks Z (X ×ₐ Y) H h
      H⊩h {L} {z} L⊩z = (F [ L ] , lem₁ , F⊩f L⊩z) , G [ L ] , lem₂ , G⊩g L⊩z
        where
          lem₁ = begin
            `projₗ (H [ L ])
              ≡⟨ refl ⟩
            (ƛ 0 · ↑₁ F ⟪ exts (subst-zero L) ⟫ · ↑₁ G ⟪ exts (subst-zero L) ⟫) · 𝑻
              ≡⟨ cong₂ (λ M N → (ƛ 0 · M · N) · 𝑻) (rename-exts (subst-zero L) F) (rename-exts (subst-zero L) G) ⟩
            (ƛ 0 · ↑₁ (F [ L ]) · ↑₁ (G [ L ])) · 𝑻
              -↠⟨ β-projₗ ⟩
            F [ L ] ∎

          lem₂ = begin
            `projᵣ (H [ L ])
              ≡⟨ refl ⟩
            (ƛ 0 · ↑₁ F ⟪ exts (subst-zero L) ⟫ · ↑₁ G ⟪ exts (subst-zero L) ⟫) · 𝑭
              ≡⟨ cong₂ (λ M N → (ƛ 0 · M · N) · 𝑭) (rename-exts (subst-zero L) F) (rename-exts (subst-zero L) G) ⟩
            (ƛ 0 · ↑₁ (F [ L ]) · ↑₁ (G [ L ])) · 𝑭
              -↠⟨ β-projᵣ ⟩
            G [ L ] ∎
------------------------------------------------------------------------------
-- Exponential object
infixr 15 _⇒_

_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_⇒_ {𝓤} X Y = (X⇒Y , X⇒YisProp) , _⊩_ , record
  { ⊩-respects-↠  = λ {x} {x′} {y} → ⊩-respects-↠ {x} {x′} {y}
  ; ⊩-right-total = ⊩-right-total
  ; ⊩-isSet       = λ {F} {f} → ⊩isSet {F} {f}
  }
    where
      open -↠-Reasoning
      module X = AsmStr (str X)
      module Y = AsmStr (str Y)

      X⇒Y = MerelyTrackable X Y
      X⇒YisProp = isSetΣ (isSetΠ (λ _ → Y is-set)) λ _ → isProp→isSet propTruncIsProp

      _⊩_ : Λ₀ → X⇒Y → 𝓤 ̇
      F ⊩ (f , _) = {M : Λ₀} {x : ⟨ X ⟩} → M X.⊩ x → (F · M Y.⊩ f x)

      postulate
        ⊩isSet : {F : Λ₀} {f : X⇒Y} → isSet (F ⊩ f)

      ⊩-respects-↠ : _⊩_ respects _-↠_ on-the-left
      ⊩-respects-↠ {G} {F} G-↠F F⊩f M⊩x = Y.⊩-respects-↠ (·ₗ-cong G-↠F) (F⊩f M⊩x)

      ⊩-right-total : _⊩_ IsRightTotal
      ⊩-right-total (f , ∃F⊩f) = rec propTruncIsProp
        (λ { (F , F⊩f) → ∣ ƛ F , (λ {M} {x} M⊩x → Y.⊩-respects-↠
          ((ƛ F) · M -→⟨ β ⟩ F [ M ] ∎) (F⊩f M⊩x)) ∣})
        ∃F⊩f
        
module Exponential (X Y : Asm 𝓤) where
  module X = AsmStr (str X)
  module Y = AsmStr (str Y)
  X⇒Y = X ⇒ Y
  module X⇒Y = AsmStr (str X⇒Y)
  open -↠-Reasoning
      
  postulate
    uncurry : {Z : Asm 𝓤} → Trackable (Z ×ₐ X) Y → Trackable Z X⇒Y
    eval : Trackable (X⇒Y ×ₐ X) Y
    {-
      uncurry {Z = Z} (f , F , F⊩f) = (λ z → (λ x → f (z , x)) , rec propTruncIsProp
        (λ { (L , L⊩z) → ∣ ↑₁ (ƛ F) · Λ.`⟨ ↑₁ L , 0 ⟩ , {!!} ∣ }) (Z.⊩-right-total z)) , 
        {!!} , {!!}
        where
          module Z = AsmStr (str Z)
      -}
