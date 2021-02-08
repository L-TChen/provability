{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude
  hiding (_∘_; id)
open import Calculus.Untyped

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
  → Λ₀
  → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y F f = {M : Λ₀} {x : ⟨ X ⟩}
  →     M X.⊩ x    
  → F · M Y.⊩ (f x)
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor hastracker

  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  field
    {F}   : Λ₀
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
id {X = X} = (λ x → x) ,
  hastracker λ M⊩x → X.⊩-respects-↠ (-→to-↠ β) M⊩x
  where
    module X = AsmStr (str X)

infixr 9 _∘_
postulate
  _∘_ : {X Y Z : Asm 𝓤} → Trackable Y Z → Trackable X Y → Trackable X Z
--_∘_ {𝓤} {X} {Y} {Z} (g , gT) (f , fT) = {!!}

-- ------------------------------------------------------------------------------
-- Universality

-- Uniqueness up to ∼ follows from function extensionality.
finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
finality (|X| , ⊩ , _isRealisable) = (λ _ → tt*) , hastracker {F = 𝑻} λ x → tt* 

-- Uniqueness up to ∼ follows from function extensionality.
initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality {𝓤} X@(|X| , _⊩_ , _isRealisable) = ⊥*-elim , hastracker {F = 𝑰} (λ { {x = ()} })

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

    postulate
      ⊩-right-total : IsRightTotal _⊩_
      {-
      ⊩-right-total (x , y) = rec propTruncIsProp
        (λ { (M , M⊩x) → rec propTruncIsProp
        (λ { (N , N⊩y) → ∣ `⟨ M , N ⟩ , M , N , {!!} , M⊩x , {!!} , N⊩y ∣ })
        (Y.⊩-right-total y)}) (X.⊩-right-total x)
      -}

projₗ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) X
projₗ X Y = (λ {(x , y) → x}) , hastracker F⊩projₗ
  where
    module X = AsmStr (str X)
    postulate
      F⊩projₗ : Tracks (X ×ₐ Y) X (ƛ ƛ # 1) λ {(x , y) → x}
      -- F⊩projₗ {M = L} {x = x , y} (M , N , projₗL-↠M , M⊩x , projᵣL-↠N , N⊩y) = X.⊩-respect-↠ {!!} M⊩x

-- Exponentia consists of trackable functions. It requires polymorphism.

--_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
--_⇒_ {𝓤} X Y = (Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥) , ⊩ , is⊩ ⊩-respects-↠ ⊩-right-total
--  where
--    module X = AsmStr (str X)
--    module Y = AsmStr (str Y)
--    
--    ⊩ : (A : 𝕋) → Prog A → Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥ → 𝓤 ̇
--    ⊩ (A `→ B) F (f , _) = (M : Prog A) (x : ⟨ X ⟩) (M⊩x : M X.⊩ x ⦂ A)
--      → Σ[ N ꞉ Prog B ] F · M -↠ N × N Y.⊩ (f x) ⦂ B 
--    ⊩ nat      F (f , _) = ⊥* {𝓤}
--    ⊩ `⊤       F (f , _) = ⊥* {𝓤} 
--    ⊩ `⊥       F (f , _) = ⊥* {𝓤}
--    ⊩ (A `× B) F (f , _) = ⊥* {𝓤}
--
--    ⊩-respects-↠ : {A : 𝕋} {G F : Prog A} {x : Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥}
--      → G -↠ F → ⊩ A F x → ⊩ A G x 
--    ⊩-respects-↠ {A = A `→ B} {G} {F} {x = (f , _)} G-↠F F⊩f M x M⊩x = N , red , P .snd .snd
--      where
--        open -↠-Reasoning
--        P : Σ[ N ꞉ Prog B ] F · M -↠ N × N Y.⊩ (f x) ⦂ B
--        P = F⊩f M x M⊩x
--        N = P .fst
--        red = begin
--          G · M -↠⟨ ·ₗ-↠ G-↠F ⟩
--          F · M -↠⟨ P .snd .fst ⟩
--          N ∎
--
--    ⊩-right-total : _
--    ⊩-right-total (f , t) = rec propTruncIsProp
--      (λ { (hastracker T F F⊩f) → {!!}}) t

-- ev : (X Y : Asm 𝓤) → Trackable ((X ⇒ Y) ×ₐ X) Y
-- ev X Y = (λ { ((f , _), x) → f x}) , ƛ `projₗ (# 0) · `projᵣ (# 0) ,
--   λ { FX ((f , _) , x) (F , M , FX-↠⟨F,M⟩ , F⊩f , M⊩x) →
--     let P : Σ[ N ꞉ _ ] F · M -↠ N × N Y.⊩ f x
--         P = F⊩f M x M⊩x
--         N     = P .fst
--         FM-↠N = P .snd .fst
--         N⊩fx  = P .snd .snd
--         red = 
--           (ƛ `projₗ (# 0) · `projᵣ (# 0)) · FX
--             -↠⟨ ·ᵣ-↠ FX-↠⟨F,M⟩ ⟩
--           (ƛ `projₗ (# 0) · `projᵣ (# 0)) · `⟨ F , M ⟩
--             -→⟨ β-ƛ· ⟩
--           `projₗ `⟨ F , M ⟩ · `projᵣ `⟨ F , M ⟩
--             -→⟨ ξ-·ₗ β-⟨,⟩`projₗ ⟩
--           F · `projᵣ `⟨ F , M ⟩
--             -→⟨ ξ-·ᵣ β-⟨,⟩`projᵣ ⟩
--           F · M
--             -↠⟨ FM-↠N ⟩
--           N ∎
--     in N , red , N⊩fx }
--   where
--     module X = AsmStr (str X)
--     module Y = AsmStr (str Y)

