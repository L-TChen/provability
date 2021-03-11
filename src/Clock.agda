{-# OPTIONS --without-K --cubical --guarded #-}

module Clock where 

open import Universes
open import Cubical.Foundations.Prelude

primitive
  primLockUniv : 𝓤₁ ̇

postulate
  Cl   : 𝓤₀ ̇
  k0   : Cl
  Tick : Cl → primLockUniv

private
  variable
    A B : 𝓤 ̇
    k   : Cl

▹ : Cl → 𝓤 ̇ → 𝓤 ̇
▹ k A = (@tick x : Tick k) → A

▸ : (k : Cl) → ▹ k (𝓤 ̇) → 𝓤 ̇
▸ k A = (@tick x : Tick k) → A x

infixr -1 ▹-syntax

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
next x _ = x

_⊛_ : ▹ k (A → B) → ▹ k A → ▹ k B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ k A → ▹ k B
map▹ f x α = f (x α)

later-ext : {f g : ▹ k A} → (▹[ α ꞉ k ] f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

pfix' : (f : ▹ k A → A) → ▹[ α ꞉ k ] dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : (▹ k A → A) → A
fix f = f (dfix f)

fix-eq : (f : ▹ k A → A) → fix f ≡ f (\ _ → fix f)
fix-eq f = \ i →  f (pfix f i)

delay : {A : Cl → Set} → (∀ k → A k) → ∀ k → ▹ k (A k)
delay a k _ = a k

Later-Alg[_]_ : Cl → 𝓤 ̇ → 𝓤 ̇
Later-Alg[ k ] A = ▹ k A → A
