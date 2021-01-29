{-# OPTIONS --without-K --cubical #-}

module Prelude where

open import Agda.Builtin.FromNat                 public
  renaming (Number to HasFromNat)

open import Cubical.Foundations.Everything       public
  hiding (id; ℓ-max)
open import Cubical.HITs.PropositionalTruncation public
  hiding (map)
  renaming (elim to truncElim)
open import Cubical.Data.Sigma                   public
open import Cubical.Data.Unit                    public
open import Cubical.Data.Empty                   public
  renaming (rec to ⊥rec; elim to ⊥-elim)
open import Cubical.Data.Bool                    public
  hiding (_≟_)
open import Cubical.Data.Nat                     public
  using (ℕ; zero; suc; _+_; fromNatℕ)
import  Cubical.Data.Nat.Order as ℕₚ
open import Cubical.Data.Fin                     public
  using (Fin; fzero; fsuc; ¬Fin0; fromNatFin)

open import Universes public
open import Later     public

private
  variable
    X Y Z : 𝓤 ̇
    A B C : 𝓤 ̇
    n m l : ℕ

infixl 8 _ˢ_
infixr 5 _∷_
infixr -1 _$_

infixr -1 Π Σ′ ∃′ _➝_


∥_∥* : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
∥_∥* {𝓥 = 𝓥} X = Lift {j = 𝓥} ∥ X ∥

pattern ∣_∣* x = lift (∣_∣ x)

------------------------------------------------------------------------
-- Π x ꞉ A , Σ a ꞉ A , ∃ a ꞉ A notation in Type Theory

syntax Π  {A = A} (λ x → b) = Π[ x ꞉ A ] b
syntax Σ′ {A = A} (λ x → b) = Σ[ x ꞉ A ] b
syntax ∃′ {A = A} (λ x → b) = ∃[ x ꞉ A ] b

Π : {A : 𝓤 ̇} (A : A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

Σ′ : {A : 𝓤 ̇} (A : A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Σ′ {A = A} B = Σ A B

∃′ : {A : 𝓤 ̇} (B : A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
∃′ {A = A} B = ∥ Σ A B ∥

_➝_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ➝ B = A → B

------------------------------------------------------------------------
-- Some simple functions

id : X → X
id x = x

------------------------------------------------------------------------
-- Operations on dependent functions


-- Application - note that _$_ is right associative, as in Haskell.
-- If you want a left associative infix application operator, use
-- Category.Functor._<$>_ from Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {B : X → 𝓤 ̇} →
      ((x : X) → B x) → ((x : X) → B x)
f $ x = f x

-- The S combinator - written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".

_ˢ_ : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {C : (x : A) → B x → 𝓦 ̇} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)

-- Instances mainly for programming instead of reasoning (subject to change)

    
-- ListLike structures
-- TODO: Use instances? 
abstract -- don't reduce []
  [] : {A : 𝓤 ̇} → Fin 0 → A
  [] {A = A} i = ⊥-elim {A = λ _ → A} (¬Fin0 i)

_∷_ : {A : 𝓤 ̇} → A → (Fin n → A) → Fin (suc n) → A
(a ∷ as) (zero  , _)     = a
(a ∷ as) (suc i , 1+i<n) = as (i , ℕₚ.pred-≤-pred 1+i<n)

[_] : {A : 𝓤 ̇} → A → Fin 1 → A
[ a ] = a ∷ []

tail : (Fin (suc n) → A) → Fin n → A
tail as n = as (fsuc n)

foldl : (B → A → B) → B → (Fin n → A) → B
foldl {n = zero}  _·_ e xs = e
foldl {n = suc n} _·_ e xs = foldl _·_ e (tail xs) · xs 0

foldl1 : (A → A → A) → (Fin (suc n) → A) → A
foldl1 {n = zero}  _·_ xs = xs 0
foldl1 {n = suc n} _·_ xs = foldl1 _·_ (tail xs) · xs 0

Fun : Universe → 𝓤ω
Fun 𝓥 = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇

IxFun : Universe → 𝓤 ̇ → 𝓤ω
IxFun 𝓥 Ix = {𝓤 : Universe} → Ix → Ix → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇

private
  variable
    F T M       : Fun 𝓥
    Ix          : 𝓤 ̇
    IxF IxT IxM : IxFun 𝓥 Ix
    i j k       : Ix

record Functor (𝓥 : Universe) (T : Fun 𝓥) : 𝓤ω where
  infixl 6 _<$>_
  field
    _<$>_ : (X → Y) → T X → T Y
  map = _<$>_
  _<$_ : Y → T X → T Y
  x <$ m = map (const x)m
open Functor ⦃...⦄ public

{-# DISPLAY Functor._<$>_ = _<$>_ #-}

instance
  truncFunc : Functor 𝓥 (∥_∥* {𝓥 = 𝓥})
  _<$>_ ⦃ truncFunc ⦄ f x = lift (Cubical.HITs.PropositionalTruncation.map f (x .lower))

record IxApplicative (𝓥 : Universe) (F : IxFun 𝓥 Ix) : 𝓤ω where
  infixl 4 _<*>_ _*>_ _<*_
  field
    pure   : X → F i i X
    _<*>_  : F i j (X → Y) → F j k X → F i k Y

  Applicative⇒Functor : Functor 𝓥 (F i j)
  _<$>_ ⦃ Applicative⇒Functor ⦄ f ma = pure f <*> ma

  _*>_ : F i j X → F j k Y → F i k Y
  fa *> fb = ⦇ (flip const) fa fb ⦈

  _<*_ : F i j X → F j k Y → F i k X
  fa <* fb = ⦇ const fa fb ⦈

  zipWith : (X → Y → Z) → F i j X → F j k Y → F i k Z
  zipWith f x y = ⦇ f x y ⦈

  zip : F i j X → F j k Y → F i k (X × Y)
  zip = zipWith _,_

  when : {𝓤 : Universe}
    → Bool → F {𝓤} i i Unit* → F {𝓤} i i Unit*
  when false s = pure tt*
  when true  s = s
open IxApplicative ⦃...⦄ public

{-# DISPLAY IxApplicative.pure  = pure  #-}
{-# DISPLAY IxApplicative._<*>_ = _<*>_ #-}
{-# DISPLAY IxApplicative._<*_  = _<*_ #-}
{-# DISPLAY IxApplicative._*>_  = _*>_ #-}
{-# DISPLAY IxApplicative.when  = when #-}

Applicative : (𝓥 : Universe) → Fun 𝓥 → 𝓤ω
Applicative 𝓥 F = IxApplicative {Ix = Unit} 𝓥 λ _ _ → F

record IxMonad (𝓥 : Universe) (M : IxFun 𝓥 Ix) : 𝓤ω where
  infixl 1 _>>=_ _>>_ _>=>_ _>>_
  infixr 1 _=<<_ _<=<_
  field
    return : X → M i i X
    _>>=_  : M i j X → (X → M j k Y) → M i k Y

  _=<<_ : (X → M j k Y) → M i j X → M i k Y
  f =<< c = c >>= f

  _>>_ : M i j X → M j k Y → M i k Y
  ma >> mb = ma >>= λ _ → mb

  _<<_ : M j k Y → M i j X → M i k Y
  mb << ma = ma >> mb

  _>=>_ : (X → M i j Y) → (Y → M j k Z) → (X → M i k Z)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (Y → M j k Z) → (X → M i j Y) → (X → M i k Z)
  g <=< f = f >=> g

  infixr 0 caseM_of_
  caseM_of_ = _>>=_

  ap : M i j (X → Y) → M j k X → M i k Y
  ap mf ma = mf >>= λ f → ma >>= λ a → return (f a)

  join : M i j (M j k X) → M i k X
  join ma = ma >>= id

  bind : M i j X → (X → M j k Y) → M i k Y
  bind = _>>=_

  bind2 : {l : Ix} → M i j X → M j k X → (X → X → M k l Y) → M i l Y
  bind2 mx₁ mx₂ _·_ = mx₁ >>= λ x₁ → mx₂ >>= λ x₂ → x₁ · x₂

  -- short-circut conditional
  ifM_then_else_ : M i j Bool → M j k X → M j k X → M i k X
  ifM mb then mx else my = caseM mb of λ where
    true  → mx
    false → my

  IxMonad⇒IxApplicative : IxApplicative 𝓥 M
  pure    ⦃ IxMonad⇒IxApplicative ⦄ = return
  _<*>_   ⦃ IxMonad⇒IxApplicative ⦄ = ap
open IxMonad ⦃...⦄ public

{-# DISPLAY IxMonad.return = return #-}
{-# DISPLAY IxMonad._>>=_  = _>>=_  #-}
{-# DISPLAY IxMonad.join   = join #-}
{-# DISPLAY IxMonad.ifM_then_else_  = ifM_then_else_ #-}

Monad : (𝓥 : Universe) → Fun 𝓥 → 𝓤ω
Monad 𝓥 M = IxMonad {Ix = Unit} 𝓥 λ _ _ → M

Monad⇒Applicative : {M : Fun 𝓥} ⦃ _ : Monad 𝓥 M ⦄ → Applicative 𝓥 M
Monad⇒Applicative {𝓥 = 𝓥} {M} = IxMonad⇒IxApplicative {M = λ _ _ → M}

instance
  Monad∥-∥ : Monad 𝓥 (∥_∥* {𝓥 = 𝓥})
  return ⦃ Monad∥-∥ ⦄ x   = lift ∣ x ∣
  _>>=_  ⦃ Monad∥-∥ ⦄ x f =
    rec (λ {(lift x) (lift y) i → lift (squash x y i)}) f (lower x)
