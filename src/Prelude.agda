{-# OPTIONS --without-K --cubical --no-import-sorts #-}

module Prelude where

open import Agda.Builtin.FromNat                 public
  renaming (Number to HasFromNat)

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          ; Set to Type
          )
infix  1 _̇

open import Cubical.Foundations.Everything       public
  hiding (id; ℓ-max; _≡⟨_⟩_; _∎; ≡⟨⟩-syntax; ⋆; ⟨_⟩; str; prop)
open import Cubical.Relation.Nullary             public
  hiding (⟪_⟫)
open import Cubical.HITs.PropositionalTruncation public
  renaming (elim to truncElim; map to ∥-∥map)

open import Cubical.Data.Sigma                     public
open import Cubical.Data.Unit                      public
open import Cubical.Data.Empty                     public
  renaming (rec to ⊥rec; elim to ⊥-elim)
open import Cubical.Data.Bool                      public
  hiding (_≟_)
open import Cubical.Data.Nat                       public
  using (ℕ; zero; suc; _+_; _∸_; fromNatℕ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive as ℕₚ public
  using (_≤_; _<_)
open import Cubical.Data.FinData                   public
  using (Fin)
  renaming (zero to fzero; suc to fsuc)

variable
  𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} → (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤
private
  variable
    A B C : 𝓤 ̇
    n m   : ℕ

infix  4  _≢_
infixr -1 _➝_
infixr -2 Π Σ′ ∃′ 

_≢_ : {A : 𝓤 ̇} → A → A → 𝓤 ̇
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Π x ∶ A , Σ a ∶ A , ∃ a ∶ A notation in Type Theory

syntax Π  {A = A} (λ x → b) = Π[ x ∶ A ] b
syntax Σ′ {A = A} (λ x → b) = Σ[ x ∶ A ] b
syntax ∃′ {A = A} (λ x → b) = ∃[ x ∶ A ] b

Π : (B : A → 𝓥 ̇) → (universe-of A) ⊔ 𝓥 ̇
Π {A = A} B = (x : A) → B x

Σ′ : (B : A → 𝓥 ̇) → (universe-of A) ⊔ 𝓥 ̇
Σ′ {A = A} B = Σ A B

∃′ : (B : A → 𝓥 ̇) → (universe-of A) ⊔ 𝓥 ̇
∃′ {A = A} B = ∥ Σ A B ∥

_➝_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ➝ B = A → B

∥_∥* : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
∥_∥* {𝓥 = 𝓥} X = ∥ Lift {j = 𝓥} X ∥

⊥*-elim : ⊥* {𝓤} → A
⊥*-elim ()

pattern ∣_∣* x = ∣ lift x ∣

isSet→ : {A : 𝓤 ̇} {B : 𝓥 ̇} → isSet B → isSet (A → B)
isSet→ pB = isSetΠ λ _ → pB

------------------------------------------------------------------------------
-- Some properties about relation

_respects_on-the-left : {A : 𝓤 ̇} {B : 𝓥 ̇}
  → (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → (_∼_ : A → A → 𝓤 ̇) → 𝓤 ⊔ 𝓥 ̇
_respects_on-the-left {𝓤} {𝓥} {A} {B} _≈_ _∼_  = {x x′ : A} {y : B} → x ∼ x′ → x′ ≈ y → x ≈ y

_respects_on-the-right : {A : 𝓤 ̇} {B : 𝓥 ̇}
  → (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → (_∼_ : B → B → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
_respects_on-the-right {𝓤} {𝓥} {A} {B} _≈_ _∼_ = {y y′ : B} {x : A} → y ∼ y′ → x ≈ y′ → x ≈ y

_IsRightTotal : {A : 𝓤 ̇} {B : 𝓥 ̇} (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
_IsRightTotal {𝓤} {𝓥} {A} {B} _≈_ = (y : B) → ∃[ x ∶ A ] (x ≈ y)

_IsLeftTotal : {A : 𝓤 ̇} {B : 𝓥 ̇} (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
_IsLeftTotal {𝓤} {𝓥} {A} {B} _≈_ = (x : A) → ∃[ y ∶ B ] (x ≈ y)

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id = λ x → x

------------------------------------------------------------------------------
-- 

SetWithStr : (𝓤 : Universe) (S : 𝓤 ̇ → 𝓥 ̇) → 𝓥 ⊔ 𝓤 ⁺ ̇
SetWithStr 𝓤 S = Σ[ X ∶ hSet 𝓤 ] S (fst X)

⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇} → SetWithStr 𝓤 S → 𝓤 ̇
⟨ (X , _) , _ ⟩ = X

str : {S : 𝓤 ̇ → 𝓥 ̇} → (X : SetWithStr 𝓤 S) → S ⟨ X ⟩
str (X , s) = s

_is-set : {S : 𝓤 ̇ → 𝓥 ̇}
  → (X : SetWithStr 𝓤 S) → isSet ⟨ X ⟩
((_ , p) , _) is-set = p


Rel : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
Rel {𝓤} {𝓥} A B = A → B → (𝓤 ⊔ 𝓥) ̇ 

MRel : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
MRel {𝓤} {𝓥} A B = Σ[ R ∶ A ➝ B ➝ (𝓤 ⊔ 𝓥) ̇ ] ((x : A) (y : B) → isProp (R x y))

------------------------------------------------------------------------------
-- 

module ≡-Reasoning where
  open import Cubical.Foundations.Prelude public
    using (_≡⟨_⟩_; ≡⟨⟩-syntax; _∎)

  infix  1 begin_
  infixr 2 _≡⟨⟩_
  
  begin_ : {x y : A} (r : x ≡ y) → x ≡ y
  begin x=y = x=y

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero  ≤? _     = yes tt
suc m ≤? zero  = no λ ()
suc m ≤? suc n = m ≤? n

strict-initial : {X : 𝓤 ̇} → (X → ⊥* {𝓤}) → X ≃ (⊥* {𝓤})
strict-initial f = f , record { equiv-proof = λ { () } }

------------------------------------------------------------------------------
-- Encode-decode method, decidable equality 

record Code (A : 𝓤 ̇) :  𝓤 ⁺ ̇ where
  field
    code   : A → A → 𝓤 ̇
    r      : (a : A)   → code a a
    decode : {a b : A} → code a b → a ≡ b

  encode : {a b : A} → a ≡ b    → code a b
  encode {a = a} a=b = transport (cong (code a) a=b) (r a)
open Code ⦃ ... ⦄ public

{-# DISPLAY Code.code x y = code x y  #-}
{-# DISPLAY Code.r x      = r x       #-}
{-# DISPLAY Code.decode c = decode c  #-}
{-# DISPLAY Code.encode p = encode p  #-}

private
  codeℕ : (m n : ℕ) → 𝓤₀ ̇
  codeℕ zero    zero    = Unit
  codeℕ (suc m) (suc n) = codeℕ m n
  codeℕ zero    (suc n) = ⊥
  codeℕ (suc m) zero    = ⊥

  rℕ : (n : ℕ) → codeℕ n n
  rℕ zero    = tt
  rℕ (suc n) = rℕ n

  decodeℕ : {m n : ℕ}
    → (codeℕ m n) → m ≡ n
  decodeℕ {zero}  {zero}  r = refl
  decodeℕ {suc m} {suc n} r = cong suc (decodeℕ r)

instance
  Codeℕ : Code ℕ
  Codeℕ = record { code = codeℕ ; r = rℕ ; decode = decodeℕ }

private
  codeFin : (i j : Fin n) → 𝓤₀ ̇
  codeFin fzero    fzero    = Unit
  codeFin (fsuc i) (fsuc j) = codeFin i j
  codeFin fzero    (fsuc _) = ⊥
  codeFin (fsuc _) fzero    = ⊥

  rFin : (i : Fin n) → codeFin i i
  rFin {n} fzero = tt
  rFin (fsuc i)  = rFin i

  decodeFin : {i j : Fin n} 
    → (r : codeFin i j)
    → i ≡ j
  decodeFin {.(suc _)} {fzero}  {fzero}  _ = refl
  decodeFin {.(suc _)} {fsuc i} {fsuc j} r = cong fsuc (decodeFin r)

instance
  CodeFin : Code (Fin n)
  CodeFin = record { code = codeFin ; r = rFin ; decode = decodeFin }
  
record IsDiscrete (A : 𝓤 ̇) : 𝓤 ̇ where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)

  ≟→isSet : isSet A
  ≟→isSet = Discrete→isSet _≟_
open IsDiscrete ⦃ ... ⦄ public

{-# DISPLAY IsDiscrete._≟_ x y = x ≟ y #-}
  
instance
  IsDiscreteUnit : IsDiscrete Unit
  IsDiscreteUnit = record { _≟_ = λ {tt tt → yes refl} }

  IsDiscreteBool : IsDiscrete Bool
  _≟_ ⦃ IsDiscreteBool ⦄ = Cubical.Data.Bool._≟_

  IsDiscreteℕ : IsDiscrete ℕ
  _≟_ ⦃ IsDiscreteℕ ⦄ = Cubical.Data.Nat.discreteℕ 

  IsDiscreteFin : IsDiscrete (Fin n)
  _≟_ ⦃ IsDiscreteFin ⦄ = Cubical.Data.FinData.discreteFin
