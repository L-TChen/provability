{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude
  hiding (_∘_; id)
open import Calculus.SystemT
open -↠-Reasoning

record IsRealisability {A : 𝕋} {X : 𝓤 ̇} (_⊩_ : Prog A → X → 𝓤 ̇) : 𝓤 ̇ where
  constructor is⊩
  field
    ⊩-respect-↠   : {M N : Prog A} {x : X} → M -↠ N → N ⊩ x → M ⊩ x 
    ⊩-right-total : (x : X) → ∃[ M ꞉ Prog A ] M ⊩ x

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    type             : 𝕋
    _⊩_              : Prog type → X → 𝓤 ̇
    ⊩isRealisability : IsRealisability _⊩_
  infix 6 _⊩_
  open IsRealisability ⊩isRealisability public

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    X Y Z : Asm 𝓤
    A B   : 𝕋

------------------------------------------------------------------------------
-- Morphisms between assemblies

module _ {𝓤 : Universe} (X Y : Asm 𝓤) where
  private
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

  Tracks : (F : X.type , ∅ ⊢ Y.type) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  Tracks F f = {M : ∅ ⊢ X.type} {x : ⟨ X ⟩} → M X.⊩ x → F [ M ] Y.⊩ f x

  record HasTracker (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
    constructor _,_
    field
      fun     : X.type , ∅ ⊢ Y.type
      tracks  : Tracks fun f 

  record Trackable : 𝓤 ̇ where
    constructor _,_
    field
      fun        : ⟨ X ⟩ → ⟨ Y ⟩
      hasTracker : HasTracker fun
    
∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , F , F⊩f) (g , G , G⊩g) = f ≡ g

infix 4 ∼-syntax

syntax ∼-syntax {X = X} {Y = Y} f g = f ∼ g ꞉ X →ₐ Y

∼-syntax : {X Y : Asm 𝓤}
  → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

id : Trackable X X
id {X = X} = (λ x → x) , # 0 , λ M⊩x → M⊩x

-- infixr 9 _∘_
-- _∘_ : {X Y Z : Asm 𝓤} → Trackable Y Z → Trackable X Y → Trackable X Z
-- _∘_ {X = X} {Y} {Z} (g , G , G⊩g) (f , F , F⊩f) = (λ x → g (f x)) , ƛ ↑ G · (↑ F · # 0) , GF⊩gf
--   where
--     module X = AsmStr (str X)
--     module Y = AsmStr (str Y)
--     module Z = AsmStr (str Z)
--     GF⊩gf : ∀ M x → M X.⊩ x → Σ[ L ꞉ Prog (Z.type) ] (ƛ ↑ G · (↑ F · # 0)) · M -↠ L × L Z.⊩ g (f x)
--     GF⊩gf M x M⊩x = 
--       let N = F⊩f M x M⊩x .fst
--           N⊩fx =  F⊩f M x M⊩x .snd .snd
--           L = G⊩g N (f x) N⊩fx .fst
--           red = begin
--             (ƛ ↑ G · (↑ F · # 0)) · M
--               -→⟨ β-ƛ· ⟩
--             ↑ G ⟪ _ ⟫ · (↑ F ⟪ _ ⟫ · M)
--               ≡⟨ cong₂ (λ N L → N · (L · M)) (subst-↑ _ G) (subst-↑ _ F) ⟩ 
--             G · (F · M)
--               -↠⟨ ·ᵣ-↠ (F⊩f M x M⊩x .snd .fst) ⟩
--             G · N
--               -↠⟨ G⊩g N (f x) N⊩fx .snd .fst ⟩
--             L
--               ∎ 
--       in L , red , G⊩g N (f x) N⊩fx .snd .snd


-- ------------------------------------------------------------------------------
-- -- Constructions

-- -- It does not seem possible to define one single ∇ : 𝓤 ̇ → Asm 𝓤
-- -- ∇₀_ : (X : 𝓤 ̇) → Asm 𝓤

-- _⊩⊥_ : Prog `⊥ → ⊥* {𝓤} → 𝓤 ̇
-- _ ⊩⊥ () 

⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , asmstr `⊥ (λ _ ()) (is⊩ (λ { {x = ()} }) λ ())

-- Uniqueness up to ∼ follows from function extensionality.
initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality (|X| , asmstr A _⊩_ _isRealisable) = (λ ()) , abort # 0  , λ { {x = ()} }

-- ⊤ₐ : Asm 𝓤
-- ⊤ₐ {𝓤 = 𝓤} = Unit* , asmstr `⊤ _⊩_  λ {tt* → ∣ `tt , tt* ∣}
--   where
--     _⊩_ : Prog `⊤ → Unit* → 𝓤 ̇
--     _ ⊩ _ = Unit*

-- -- Uniqueness up to ∼ follows from function extensionality.
-- finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
-- finality X = (λ _ → tt*) , ƛ `tt , λ M _ _ →
--   let red = begin
--         (ƛ `tt) · M
--           -→⟨ β-ƛ· ⟩
--         `tt [ M ]
--           ≡⟨ refl ⟩
--         `tt ∎
--   in `tt , red , tt*

-- ℕₐ : Asm₀
-- ℕₐ = ℕ , asmstr nat _⊩_ realisable
--   where
--     _⊩_ : Prog nat → ℕ → 𝓤₀ ̇
--     M ⊩ zero  = M -↠ `zero
--     M ⊩ suc n = Σ[ N ꞉ Prog nat ] N ⊩ n × M -↠ `suc N

--     realisable : Π[ n ꞉ ℕ ] ∃[ M ꞉ Prog nat ] (M ⊩ n)
--     realisable zero    = ∣ `zero , -↠-refl ∣
--     realisable (suc n) = rec propTruncIsProp
--       (λ {(N , N⊩n) → ∣ `suc N , N , N⊩n , -↠-refl ∣  })
--       (realisable n)
    
-- _×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
-- X ×ₐ Y = ⟨ X ⟩ × ⟨ Y ⟩ , asmstr (X.type `× Y.type) _⊩_ realisable
--   where
--     module X = AsmStr (str X)
--     module Y = AsmStr (str Y)

--     _⊩_ : Prog (X.type `× Y.type) → ⟨ X ⟩ × ⟨ Y ⟩ → _
--     L ⊩ (x , y) = Σ[ M ꞉ Prog X.type ] Σ[ N ꞉ Prog Y.type ] L -↠ `⟨ M , N ⟩ × M X.⊩ x × N Y.⊩ y

--     realisable : Π[ z ꞉ ⟨ X ⟩ × ⟨ Y ⟩ ] ∃[ a ꞉ Prog (X.type `× Y.type) ] a ⊩ z
--     realisable (x , y) = rec propTruncIsProp
--       (λ { (M , M⊩x) → rec propTruncIsProp
--         (λ {(N , N⊩y) → ∣ `⟨ M , N ⟩ , M , N , -↠-refl , M⊩x , N⊩y ∣ }) (y Y.isRealisable) })
--         (x X.isRealisable)

-- projₗ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) X
-- projₗ X Y = (λ { (x , y) → x}) , ƛ `projₗ (# 0) ,
--   λ {MN (x , y) (M , N , MN-↠‵⟨M,N⟩ , M⊩x , _) →
--     let red = begin
--           (ƛ `projₗ (# 0)) · MN
--             -→⟨ β-ƛ· ⟩
--           `projₗ MN
--             -↠⟨ `projₗ-↠ MN-↠‵⟨M,N⟩ ⟩
--           `projₗ `⟨ M , N ⟩
--             -→⟨ β-⟨,⟩`projₗ ⟩
--           M ∎
--     in M , red , M⊩x}

-- -- Exponentia consists of trackable functions

-- _⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
-- X ⇒ Y = (Σ[ f ꞉ (⟨ X ⟩ → ⟨ Y ⟩) ] ∥ HasTracker X Y f ∥) ,
--   asmstr (X.type `→ Y.type) _⊩_ realisable
--   where
--     module X = AsmStr (str X)
--     module Y = AsmStr (str Y)
--     _⊩_ : Prog (X.type `→ Y.type) → _ → universe-of ⟨ X ⟩ ̇ 
--     F ⊩ (f , _) = Π[ M ꞉ Prog X.type ] Π[ x ꞉ ⟨ X ⟩ ]
--       (M X.⊩ x → Σ[ N ꞉ Prog Y.type ] F · M -↠ N × N Y.⊩ f x)
      
--     realisable : ∀ f → ∃[ F ꞉ Prog _ ] F ⊩ f
--     realisable (f , fhasTracker) = rec propTruncIsProp
--       (λ { (F , F⊩f) → ∣ F , F⊩f ∣ })
--       fhasTracker

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

