{-# OPTIONS --guarded  #-}

module Assembly.ClockedExposure where

open import Prelude
  hiding (id; _∘_)
open import Later
open import Calculus.Untyped

open import Assembly.Base
open import Assembly.Properties

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Endo-exposure

record IsCloExpo (Q : Cl → Asm 𝓤 → Asm 𝓤) (map : {X Y : Asm 𝓤} → (k : Cl) → Trackable X Y → Trackable (Q k X) (Q k Y)) : 𝓤 ⁺ ̇ where 
  field
    preserve-id   : {k : Cl} → (X : Asm 𝓤)
      → map k (id X) ∼ id (Q k X)
    preserve-comp : {k : Cl} (f : Trackable X Y) (g : Trackable Y Z)
      → map k (g ∘ f) ∼ map k g ∘ map k f
    reflects-∼    : (f g : Trackable X Y)
      → (∀ k → map k f ∼ map k g)
      → (k : Cl) →   f ∼ g    

record CloExpo (𝓤 : Universe) : 𝓤 ⁺ ̇ where
  constructor exposure
  field
    obj        : Cl → Asm 𝓤 → Asm 𝓤
    map        : {X Y : Asm 𝓤} → (k : Cl) → Trackable X Y → Trackable (obj k X) (obj k Y)
    isExposure : IsCloExpo obj map
open CloExpo


record NaturalTransformation (P Q : CloExpo 𝓤) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    fun        : (k : Cl) → (X : Asm 𝓤) → Trackable (P .obj k X) (Q .obj k X) 
    naturality : {k : Cl} → {X Y : Asm 𝓤} → (f : Trackable X Y)
      → (fun k Y) ∘ P .map k f ∼ Q .map k f ∘ (fun k X)

Id : CloExpo 𝓤
Id = exposure (λ _ X → X) (λ _ f → f) record
  { preserve-id   = λ _ x   → refl
  ; preserve-comp = λ f g x → refl
  ; reflects-∼    = λ f g f=g k x → f=g k x
  }
