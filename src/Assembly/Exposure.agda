{-# OPTIONS --without-K --cubical #-}

module Assembly.Exposure where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub)
open import Calculus.Untyped

open import Assembly.Base
open import Assembly.Properties

------------------------------------------------------------------------------
-- Endo-exposure

record IsExposure (Q : Asm 𝓤 → Asm 𝓤) (map : {X Y : Asm 𝓤} → Trackable X Y → Trackable (Q X) (Q Y)) : 𝓤 ⁺ ̇ where 
  field
    preserve-id   : (X : Asm 𝓤)
      → map (id X) ∼ id (Q X)
    preserve-comp : {X Y Z : Asm 𝓤} (f : Trackable X Y) (g : Trackable Y Z)
      → map (g ∘ f) ∼ map g ∘ map f
    reflects-∼    : {X Y : Asm 𝓤} (f g : Trackable X Y)
      → map f ∼ map g 
      →     f ∼ g    

record Exposure (𝓤 : Universe) : 𝓤 ⁺ ̇ where
  constructor exposure
  field
    obj        : Asm 𝓤 → Asm 𝓤
    map        : {X Y : Asm 𝓤} → Trackable X Y → Trackable (obj X) (obj Y)
    isExposure : IsExposure obj map
open Exposure

Naturality : (P Q : Exposure 𝓤) → ({X : Asm 𝓤} → Trackable (P .obj X) (Q .obj X)) → 𝓤 ⁺ ̇
Naturality {𝓤} P Q fun = {X Y : Asm 𝓤} → (f : Trackable X Y) → fun ∘ P .map f ∼ Q .map f ∘ fun

record NaturalTransformation (P Q : Exposure 𝓤) : 𝓤 ⁺ ̇ where
  constructor _,_
  field
    fun        : {X : Asm 𝓤} → Trackable (P .obj X) (Q .obj X) 
    naturality : Naturality P Q fun

Id : Exposure 𝓤
Id = exposure (λ X → X) (λ f → f) record
  { preserve-id   = λ _ x   → refl
  ; preserve-comp = λ f g x → refl
  ; reflects-∼    = λ _ _ x → x
  }

