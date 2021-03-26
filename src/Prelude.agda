{-# OPTIONS --without-K --cubical --no-import-sorts #-}

module Prelude where

open import Agda.Builtin.FromNat                 public
  renaming (Number to HasFromNat)

open import Cubical.Foundations.Everything       public
  hiding (id; ℓ-max; _≡⟨_⟩_; _∎; ≡⟨⟩-syntax; ⋆; ⟨_⟩; str)
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

open import Prelude.Universes public
open import Prelude.Notations public
open import Prelude.Instances public


private
  variable
    A B C : 𝓤 ̇
    n m   : ℕ

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
_IsRightTotal {𝓤} {𝓥} {A} {B} _≈_ = (y : B) → ∃[ x ꞉ A ] (x ≈ y)

_IsLeftTotal : {A : 𝓤 ̇} {B : 𝓥 ̇} (_≈_ : A → B → 𝓤 ⊔ 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
_IsLeftTotal {𝓤} {𝓥} {A} {B} _≈_ = (x : A) → ∃[ y ꞉ B ] (x ≈ y)

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id = λ x → x

------------------------------------------------------------------------------
-- 

instance
  hSet→Type : Coercion (hSet 𝓤) (𝓤 ̇)
  hSet→Type = record { ⟨_⟩ = fst }

  hProp→Type : Coercion (hProp 𝓤) (𝓤 ̇)
  hProp→Type = record { ⟨_⟩ = fst }
  
  TypeStr→Type : {S : 𝓤 ̇ → 𝓥 ̇} → Coercion (TypeWithStr 𝓤 S) (𝓤 ̇)
  TypeStr→Type = record { ⟨_⟩ = fst }

------------------------------------------------------------------------------
-- 

record SetWithStr (𝓤 : Universe) (S : 𝓤 ̇ → 𝓥 ̇) : 𝓥 ⊔ 𝓤 ⁺ ̇ where
  constructor _,_
  field
    carrier   : hSet 𝓤
    structure : S ⟨ carrier ⟩

  toTypeStr : TypeWithStr 𝓤 S
  toTypeStr = ⟨ carrier ⟩ , structure

  _is-set : isSet ⟨ carrier ⟩
  _is-set = carrier .snd

open SetWithStr public
  renaming (structure to str)

module _ {S : 𝓤 ̇ → 𝓥 ̇} where
  instance
    SetStr→Type : Coercion (SetWithStr 𝓤 S) (𝓤 ̇)
    ⟨_⟩ ⦃ SetStr→Type ⦄ (carrier , _) = ⟨ carrier ⟩

--    SetStr→TypeStr : Coercion (SetWithStr 𝓤 S) (TypeWithStr 𝓤 S)
--    ⟨_⟩ ⦃ SetStr→TypeStr ⦄ (carrier , str) = ⟨ carrier ⟩ , str

Rel : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
Rel {𝓤} {𝓥} A B = A → B → (𝓤 ⊔ 𝓥) ̇ 

MRel : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ⁺ ̇
MRel {𝓤} {𝓥} A B = Σ[ R ꞉ A ➝ B ➝ (𝓤 ⊔ 𝓥) ̇ ] ((x : A) (y : B) → isProp (R x y))

instance
  MRel→Rel : Coercion (MRel A B) (Rel A B)
  MRel→Rel = record { ⟨_⟩ = fst }

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
  
instance
  IsDiscreteUnit : IsDiscrete Unit
  IsDiscreteUnit = record { _≟_ = λ {tt tt → yes refl} }

  IsDiscreteBool : IsDiscrete Bool
  _≟_ ⦃ IsDiscreteBool ⦄ = Cubical.Data.Bool._≟_

  IsDiscreteℕ : IsDiscrete ℕ
  _≟_ ⦃ IsDiscreteℕ ⦄ = Cubical.Data.Nat.discreteℕ 

  IsDiscreteFin : IsDiscrete (Fin n)
  _≟_ ⦃ IsDiscreteFin ⦄ = Cubical.Data.FinData.discreteFin
