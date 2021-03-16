{-# OPTIONS --without-K --cubical --guarded #-}

-- Most of definitions are from LaterPrims.agda

module Later where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Universes 

module Prims where
  primitive
    primLockUniv : 𝓤₁ ̇
open Prims renaming (primLockUniv to LockU) public

infixl 4 _⊛_
infixr -1 ▹-syntax

postulate
  Cl   : 𝓤₀ ̇
  k0   : Cl
  Tick : Cl → LockU
  
private
  variable
    A : 𝓤 ̇
    B : A → 𝓤 ̇
    k   : Cl

▹ : Cl → 𝓤 ̇ → 𝓤 ̇
▹ k A = (@tick x : Tick k) → A

▸ : (k : Cl) → ▹ k (𝓤 ̇) → 𝓤 ̇
▸ k A = (@tick x : Tick k) → A x

▹-syntax : (k : Cl) → ▹ k (𝓤 ̇) → 𝓤 ̇
▹-syntax k A = (@tick α : Tick k) → A α

syntax ▹-syntax k (λ α → e) = ▹[ α ꞉ k ] e

postulate
  tick-irr : {k : Cl} (x : ▹ k A) → ▹[ α ꞉ k ] ▹[ β ꞉ k ] x α ≡ x β

postulate
  dfix : (▹ k A → A) → ▹ k A
  pfix : (f : ▹ k A → A) → dfix f ≡ (\ _ → f (dfix f))

  force       : {A : Cl → 𝓤 ̇}        → (∀ k → ▹ k (A k)) → ∀ k → A k
  force-delay : {A : Cl → 𝓤 ̇}        → (f : ∀ k → ▹ k (A k)) → ∀ k → ▹[ α ꞉ k ] force f k ≡ f k α
  delay-force : {A : Cl → 𝓤 ̇}        → (f : ∀ k → A k)       → ∀ k → force (\ k α → f k) k ≡ f k
  force^      : {A : ∀ k → ▹ k (𝓤 ̇)} → (∀ k → ▸ k (A k))     → ∀ k → force A k
-- No more postulates after this line.

next : A → ▹ k A
next x k = x

_⊛_ : ▹ k ((a : A) → B a)
  → (a : ▹ k A) → ▹[ α ꞉ k ] B (a α)
(f ⊛ x) k = f k (x k)

▹map : ((a : A) → B a)
  → (a : ▹ k A) → ▹[ α ꞉ k ] B (a α)
▹map f x k = f (x k)

Σ▹
  : Σ (▹ k A) (λ ▹x → ▹[ α ꞉ k ] B (▹x α))
  → ▹[ α ꞉ k ] Σ[ a ∈ A ] B a
Σ▹ (x , y) α = (x α) , (y α)

▹Σ
  : ▹[ α ꞉ k ] Σ[ a ∈ A ] B a
  → Σ (▹ k A) λ ▹x → ▹[ α ꞉ k ] B (▹x α)
▹Σ f = (λ α → fst (f α)) , λ α → snd (f α)


▹-extensionality : {A : I → 𝓤 ̇} {x : ▹ k (A i0)} {y : ▹ k (A i1)}
  → ▹[ α ꞉ k ] PathP A (x α) (y α) → PathP (λ i → ▹ k (A i)) x y
▹-extensionality p i α = p α i

▹isProp→isProp▹ : {A : ▹ k (𝓤 ̇)}
  → ▹[ α ꞉ k ] isProp (A α)
  → isProp (▹[ α ꞉ k ] (A α))
▹isProp→isProp▹ p x y = λ i α → p α (x α) (y α) i

transp▹ : (A : I → ▹ k (𝓤 ̇)) → ▸ k (A i0) → ▸ k (A i1)
transp▹ {k = k} A = transp (λ i → ▸ k (A i)) i0

hcomp▹ : (A : ▹ k (𝓤 ̇)) (φ : I) (u : I → Partial φ (▸ k A))
  → (u0 : ▸ k A [ φ ↦ u i0 ]) → ▸ k A
hcomp▹ A φ u u0 a = hcomp (λ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

fix : (▹ k A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ k A → A) → fix f ≡ f (next (fix f))
fix-path f i = f (pfix f i)

delay : {A : Cl → Set} → (∀ k → A k) → ∀ k → ▹ k (A k)
delay a k _ = a k
