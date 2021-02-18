{-# OPTIONS --without-K --cubical --guarded #-}

module Assembly.Exposure where

open import Prelude           as 𝓤
  hiding (id; _∘_; Sub)
open import Calculus.Untyped
  hiding (Z)
open import Assembly.Base

private
  variable
    X Y Z : Asm 𝓤
------------------------------------------------------------------------------
-- Endo-exposure

record IsEndoExposure (Q : Asm 𝓤 → Asm 𝓤) : 𝓤 ⁺ ̇ where 
  constructor is-exposure
  field
    map           : Trackable X Y → Trackable (Q X) (Q Y)
    preserve-id   : {X : Asm 𝓤}
      → map id ∼ id ꞉ Q X →ₐ Q X
    preserve-comp : {f : Trackable X Y} {g : Trackable Y Z}
      → map g ∘ map f ∼ map (g ∘ f) ꞉ Q X →ₐ Q Z
    reflects-∼    : {f g : Trackable X Y}
      → map f ∼ map g ꞉ Q X →ₐ Q Y
      →     f ∼ g     ꞉ X   →ₐ Y

