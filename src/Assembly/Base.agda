{-# OPTIONS --without-K --cubical #-}

module Assembly.Base where

open import Prelude
  hiding (_∘_; id)
open import Calculus.SystemT

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    type          : 𝕋
    _⊩_           : Prog type → X → 𝓤 ̇
    _isRealisable : Π[ x ꞉ X ] ∃[ M ꞉ Prog type ] M ⊩ x
  infix 6 _⊩_

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁ ̇
Asm₀ = Asm 𝓤₀

private
  variable
    X Y Z : Asm 𝓤

------------------------------------------------------------------------------
-- Morphisms between assemblies

record HasTracker (X Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where
  constructor _,_
  
  module X = AsmStr (str X)
  module Y = AsmStr (str Y)

  _tracks_ : Prog (X.type `→ Y.type) → (⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇
  F tracks f = Π[ M ꞉ Prog X.type ] Π[ x ꞉ ⟨ X ⟩ ] (M X.⊩ x → Σ[ N ꞉ Prog Y.type ] F · M -↠ N × N Y.⊩ f x)
  -- TODO: does N merely exist? 

  field
    realiser      : Prog (X.type `→ Y.type)
    _isRealisable : realiser tracks f

record Trackable (X Y : Asm 𝓤) : 𝓤  ̇ where
  constructor _,_
  field
    fun        : ⟨ X ⟩ → ⟨ Y ⟩
    hasTracker : HasTracker X Y fun
open Trackable
    
∼-eq : (X Y : Asm 𝓤) → (f g : Trackable X Y) → 𝓤 ̇
∼-eq X Y (f , F , F⊩f) (g , G , G⊩g) = f ≡ g

infix 4 ∼-syntax

syntax ∼-syntax {X = X} {Y = Y} f g = f ∼ g ꞉ X →ₐ Y

∼-syntax : {X Y : Asm 𝓤} → (f g : Trackable X Y) → 𝓤 ̇
∼-syntax {X = X} {Y = Y} f g = ∼-eq X Y f g

id : Trackable X X
id {X = (|X| , asmX)} =
  (λ (x : |X|) → x) ,
  𝐼 ,
  λ M x M⊩x → M , -→to-↠ β-ƛ· , M⊩x

infixr 9 _∘_
_∘_ : {X Y Z : Asm 𝓤} → Trackable Y Z → Trackable X Y → Trackable X Z
_∘_ {X = X} {Y} {Z} (g , G , G⊩g) (f , F , F⊩f) = (λ x → g (f x)) , ƛ ↑ G · (↑ F · # 0) , GF⊩gf
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)
    module Z = AsmStr (str Z)
    GF⊩gf : ∀ M x → M X.⊩ x → Σ[ L ꞉ Prog (Z.type) ] (ƛ ↑ G · (↑ F · # 0)) · M -↠ L × L Z.⊩ g (f x)
    GF⊩gf M x M⊩x = L , red , L⊩gfx
      where
        N : Prog Y.type
        N = F⊩f M x M⊩x .fst
        N⊩fx : N Y.⊩ (f x)
        N⊩fx =  F⊩f M x M⊩x .snd .snd

        L : Prog Z.type
        L = G⊩g N (f x) N⊩fx .fst
        L⊩gfx : L Z.⊩ (g (f x))
        L⊩gfx = G⊩g N (f x) N⊩fx .snd .snd
        
        open -↠-Reasoning
        red : (ƛ ↑ G · (↑ F · # 0)) · M -↠ L
        red = begin
          (ƛ ↑ G · (↑ F · # 0)) · M
            -→⟨ β-ƛ· ⟩
          ↑ G ⟪ _ ⟫ · (↑ F ⟪ _ ⟫ · M)
            ≡⟨ cong₂ (λ N L → N · (L · M)) (subst-↑ _ G) (subst-↑ _ F) ⟩ 
          G · (F · M)
            -↠⟨ ·ᵣ-↠ (F⊩f M x M⊩x .snd .fst) ⟩
          G · N
            -↠⟨ G⊩g N (f x) N⊩fx .snd .fst ⟩
          L
            ∎ 


------------------------------------------------------------------------------
-- Constructions

_⊩⊥_ : Prog `⊥ → ⊥* {𝓤} → 𝓤 ̇
_ ⊩⊥ () 

⊥ₐ : Asm 𝓤
⊥ₐ = ⊥* , asmstr `⊥ _⊩⊥_ λ ()

-- Uniqueness up to ∼ follows from function extensionality.
initiality : (X : Asm 𝓤) → Trackable ⊥ₐ X
initiality (|X| , asmstr A _⊩_ _isRealisable) = (λ ()) , ƛ abort # 0  , λ _ ()

⊤ₐ : Asm 𝓤
⊤ₐ {𝓤 = 𝓤} = Unit* , asmstr `⊤ _⊩_  λ {tt* → ∣ `tt , tt* ∣}
  where
    _⊩_ : Prog `⊤ → Unit* → 𝓤 ̇
    _ ⊩ _ = Unit*

-- Uniqueness up to ∼ follows from function extensionality.
finality : (X : Asm 𝓤) → Trackable X ⊤ₐ
finality X = (λ _ → tt*) , ƛ `tt , λ M _ _ → `tt , red M , tt*
  where
    open -↠-Reasoning
    red : ∀ {A} (M : Prog A) → (ƛ `tt) · M -↠ `tt
    red M = begin
      (ƛ `tt) · M
        -→⟨ β-ƛ· ⟩
      `tt [ M ]
        ≡⟨ refl ⟩
      `tt ∎

ℕₐ : Asm₀
ℕₐ = ℕ , asmstr nat _⊩_ realisable
  where
    _⊩_ : Prog nat → ℕ → 𝓤₀ ̇
    M ⊩ zero  = M -↠ zero
    M ⊩ suc n = Σ[ N ꞉ Prog nat ] N ⊩ n × M -↠ suc N

    realisable : Π[ n ꞉ ℕ ] ∃[ M ꞉ Prog nat ] (M ⊩ n)
    realisable zero    = ∣ zero , -↠-refl ∣
    realisable (suc n) = rec propTruncIsProp
      (λ {(N , N⊩n) → ∣ suc N , N , N⊩n , -↠-refl ∣  })
      (realisable n)
    
_×ₐ_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
X ×ₐ Y = ⟨ X ⟩ × ⟨ Y ⟩ , asmstr (X.type `× Y.type) _⊩_ realisable
  where
    module X = AsmStr (str X)
    module Y = AsmStr (str Y)

    _⊩_ : Prog (X.type `× Y.type) → ⟨ X ⟩ × ⟨ Y ⟩ → _
    L ⊩ (x , y) = Σ[ M ꞉ Prog X.type ] Σ[ N ꞉ Prog Y.type ] L -↠ `⟨ M , N ⟩ × M X.⊩ x × N Y.⊩ y

    realisable : Π[ z ꞉ ⟨ X ⟩ × ⟨ Y ⟩ ] ∃[ a ꞉ Prog (X.type `× Y.type) ] a ⊩ z
    realisable (x , y) = rec propTruncIsProp
      (λ { (M , M⊩x) → rec propTruncIsProp
        (λ {(N , N⊩y) → ∣ `⟨ M , N ⟩ , M , N , -↠-refl , M⊩x , N⊩y ∣ }) (y Y.isRealisable) })
        (x X.isRealisable)

--_⇒_ : Asm 𝓤 → Asm 𝓤 → Asm 𝓤
--X ⇒ Y = Trackable , asmstr (A →̇ B) _⊩_ {!!} -- (⟨ X ⟩ → ⟨ Y ⟩) , asmstr (A →̇ B) (Mor._tracks_ X Y) {!i!}
--  where
--    open Mor X Y
--    open AsmStr (str X) renaming (type to A; _⊩_ to _⊩x_)
--    open AsmStr (str Y) renaming (type to B; _⊩_ to _⊩y_)
--
--    _⊩_ : Prog (A →̇ B) → Trackable → _
--    F ⊩ (f , r , r⊩f) = Lift (F ≡ r)

-- The type (Prog A) of programs of type A is itself an assembly with α-equality
𝔗 : 𝕋 → Asm 𝓤₀
𝔗 A = Prog A , asmstr A _≡_ λ M → ∣ M , refl ∣

-- It does not seem possible to define one single ∇ : 𝓤 ̇ → Asm 𝓤
-- ∇₀_ : (X : 𝓤 ̇) → Asm 𝓤

