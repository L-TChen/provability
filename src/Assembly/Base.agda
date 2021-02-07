{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude as 𝓤
  hiding (_∘_; id)
open import Calculus.SystemT
open -↠-Reasoning

record IsRealisability {X : 𝓤 ̇} (⊩ : (A : 𝕋) → Prog A → X → 𝓤 ̇) : 𝓤 ̇ where
  constructor is⊩
  field
    ⊩-respect-↠   : {A : 𝕋} {M N : Prog A} {x : X} → M -↠ N → ⊩ A N x → ⊩ A M x 
    ⊩-right-total : (x : X) → ∃[ A ꞉ 𝕋 ] Σ[ M ꞉ Prog A ] ⊩ A M x 

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    ⊩               : (A : 𝕋) → Prog A → X → 𝓤 ̇
    isRealisability : IsRealisability ⊩
  open IsRealisability isRealisability public

  ⊩-syntax = ⊩
  infix 6 ⊩-syntax
  syntax ⊩-syntax A M x = M ⊩ x ⦂ A

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    A B   : 𝕋
    X Y Z : Asm 𝓤
    x y z : ⟨ X ⟩

------------------------------------------------------------------------------
-- Examples
∇_ : (X : 𝓤 ̇) → Asm 𝓤
∇ X = X , (λ _ _ _ → Unit*) , is⊩ (λ _ _ → tt*) λ x → ∣ `⊤ , `tt , tt* ∣

⊩⊥ : (A : 𝕋) → Prog A → ⊥* {𝓤} → 𝓤 ̇
⊩⊥ _ _ ()

⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , ⊩⊥ , is⊩ (λ { {x = ()} }) λ ()

⊤ₐ : Asm 𝓤
⊤ₐ = ∇ Unit* 

------------------------------------------------------------------------------
-- Morphisms between assemblies

Tracks : (X Y : Asm 𝓤) {T : 𝕋 → 𝕋}
  → (F : ∀ {A} → A , ∅ ⊢ T A)
  → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
Tracks X Y {T} F f = {A : 𝕋} {M : Prog A} {x : ⟨ X ⟩}
  →       M X.⊩ x     ⦂ A
  → F [ M ] Y.⊩ (f x) ⦂ T A
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor hastracker

  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  field
    T   : 𝕋 → 𝕋
    F   : ∀ {A} → A , ∅ ⊢ T A
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
id {X = |X| , ⊩ , _isRealisable} = (λ x → x) ,
  hastracker (λ A → A) (# 0) λ M⊩x → M⊩x

infixr 9 _∘_
postulate
  _∘_ : {X Y Z : Asm 𝓤} → Trackable Y Z → Trackable X Y → Trackable X Z
--_∘_ {𝓤} {X} {Y} {Z} (g , gT) (f , fT) = g 𝓤.∘ f , hastracker (g.T 𝓤.∘ f.T)
--  {!!} -- cut rule 
--  {!!} -- substitution lemma
--  where
--    module X = AsmStr (str X)
--    module Y = AsmStr (str Y)
--    module Z = AsmStr (str Z)
--    module g = HasTracker gT
--    module f = HasTracker fT

-- ------------------------------------------------------------------------------
-- Universality

-- Uniqueness up to ∼ follows from function extensionality.
finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
finality (|X| , ⊩ , _isRealisable) = (λ _ → tt*) , hastracker _ `tt λ M⊩x → tt*

-- -- Uniqueness up to ∼ follows from function extensionality.
initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality {𝓤} X@(|X| , _⊩_ , _isRealisable) = ⊥*-elim , hastracker _ `zero (λ { {x = ()} })

⊩ℕ : (A : 𝕋) → Prog A → ℕ → 𝓤₀ ̇
⊩ℕ nat M zero    = M -↠ `zero
⊩ℕ nat M (suc n) = Σ[ N ꞉ Prog nat ] M -↠ `suc N × ⊩ℕ nat N n
⊩ℕ A   M n       = ⊥

⊩ℕ-respect-↠ : {A : 𝕋} {M N : Prog A} {x : ℕ}
   → M -↠ N → ⊩ℕ A N x → ⊩ℕ A M x
⊩ℕ-respect-↠ {A = nat}    {x = zero}  M-↠N N⊩x                    = _ -↠⟨ M-↠N ⟩ _ -↠⟨ N⊩x ⟩ `zero ∎
⊩ℕ-respect-↠ {A = nat}    {x = suc x} M-↠N (N′ , N-↠sucN′ , N′⊩x) = N′ , _ -↠⟨ M-↠N ⟩ _ -↠⟨ N-↠sucN′ ⟩ `suc N′ ∎ , N′⊩x
⊩ℕ-respect-↠ {A = `⊤}                 _    () 
⊩ℕ-respect-↠ {A = `⊥}                 _    ()
⊩ℕ-respect-↠ {A = _ `× _}             _    ()
⊩ℕ-respect-↠ {A = _ `→ _}             _    ()

⊩ℕ-right-total : (n : ℕ) → ∃[ A ꞉ 𝕋 ] Σ[ M ꞉ Prog A ] ⊩ℕ A M n
⊩ℕ-right-total zero    = ∣ nat , `zero , -↠-refl ∣
⊩ℕ-right-total (suc n) = rec propTruncIsProp
  (λ { (nat , N , N⊩n) → ∣ nat , `suc N , N , -↠-refl , N⊩n ∣ })
  (⊩ℕ-right-total n)

ℕₐ : Asm₀
ℕₐ = ℕ , ⊩ℕ , is⊩ ⊩ℕ-respect-↠ ⊩ℕ-right-total
    
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
_×ₐ_ {𝓤} X Y = ⟨ X ⟩ × ⟨ Y ⟩ , ⊩ , is⊩ ⊩-respect-↠ ⊩-right-total
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    ⊩ : (A : 𝕋) → Prog A → ⟨ X ⟩ × ⟨ Y ⟩ → 𝓤 ̇
    ⊩ (A `× B) L (x , y) = Σ[ M ꞉ Prog A ] Σ[ N ꞉ Prog B ]
      L -↠ `⟨ M , N ⟩ × M X.⊩ x ⦂ A × N Y.⊩ y ⦂ B
    ⊩ _        _ _       = ⊥*

    ⊩-respect-↠   : {A : 𝕋} {M N : Prog A} {z : ⟨ X ⟩ × ⟨ Y ⟩}
      → M -↠ N → ⊩ A N z → ⊩ A M z
    ⊩-respect-↠ {A = _ `× _} {z = x , y} M-↠N (M , N , L-↠⟨M,N⟩ , M⊩x , N⊩y) = M , N , -↠-trans M-↠N L-↠⟨M,N⟩ , M⊩x , N⊩y
    ⊩-respect-↠ {A = nat}                _    ()
    ⊩-respect-↠ {A = `⊤}                 _    ()
    ⊩-respect-↠ {A = `⊥}                 _    ()
    ⊩-respect-↠ {A = _ `→ _}             _    ()

    ⊩-right-total : (z : ⟨ X ⟩ × ⟨ Y ⟩) → ∃[ A ꞉ 𝕋 ] Σ[ M ꞉ Prog A ] ⊩ A M z
    ⊩-right-total (x , y) = rec propTruncIsProp
      (λ { (A , M , M⊩x) → rec propTruncIsProp
      (λ { (B , N , N⊩y) → ∣ A `× B , `⟨ M , N ⟩ , M , N , -↠-refl , M⊩x , N⊩y ∣ })
      (Y.⊩-right-total y)}) (X.⊩-right-total x)

projₗ : (X Y : Asm 𝓤) → Trackable (X ×ₐ Y) X
projₗ X Y = (λ {(x , y) → x}) , hastracker T F F⊩projₗ
  where
    module X = AsmStr (str X)
    T : 𝕋 → 𝕋
    T (A `× _) = A
    T _        = `⊤

    F : {A : 𝕋} → A , ∅ ⊢ T A
    F {A = A `× _}  = `projₗ (# 0)
    F {A = nat}     = `tt
    F {A = `⊤}      = `tt
    F {A = `⊥}      = `tt
    F {A = _ `→ _}  = `tt

    F⊩projₗ : Tracks (X ×ₐ Y) X F λ {(x , y) → x}
    F⊩projₗ {A = A `× B} (M , N , L-→⟨M,N⟩ , M⊩x , N⊩y) = X.⊩-respect-↠ red M⊩x
      where
        red = begin 
          `projₗ _
            -↠⟨ `projₗ-↠ L-→⟨M,N⟩ ⟩
          `projₗ `⟨ M , N ⟩
            -→⟨ β-⟨,⟩`projₗ ⟩
          M ∎

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

