{-# OPTIONS --without-K --cubical #-}


open import Prelude
open import Cubical.HITs.PropositionalTruncation
import Cubical.Data.Empty                   as E

open import Algebra.PCA

{- The notion of assembly is defined over a fixed partial combinatory algebra -}

module Assembly.Base (A : PCA 𝓤₀) where

open PcaStr (str A)

record IsAssembly {X : 𝓤 ̇} (_⊩_ : ⟨ A ⟩ → X → 𝓤 ̇) : 𝓤 ̇ where 
  constructor isasm
  field
    isRealisable : (x : X) → ∃[ a ∈ ⟨ A ⟩ ] (a ⊩ x)
    ⊩isProp      : (a : ⟨ A ⟩) (x : X) → isProp (a ⊩ x)

record AsmStr (X : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  constructor asmstr
  field
    _⊩_        : ⟨ A ⟩ → X → 𝓤 ̇
    isAssembly : IsAssembly _⊩_

  open IsAssembly isAssembly

Asm : (𝓤 : Level) → 𝓤 ⁺ ̇
Asm 𝓤 = TypeWithStr 𝓤 AsmStr

Asm₀ : 𝓤₁  ̇
Asm₀ = Asm 𝓤₀

⊥ : Asm₀
⊥ = E.⊥ , asmstr (λ _ ()) (isasm (λ ()) λ _ ()) 

□ : Asm 𝓤 → Asm 𝓤
□ (X , asmstr _⊩_ isAssembly) = (Σ[ a ∈ ⟨ A ⟩ ] Σ[ x ∈ X ] (a ⊩ x)) , asmstr (λ a b → Lift (a ≡ fst b))
  (isasm (λ { (a , x , a⊩x) → ∣ a , lift refl ∣}) {!!})

record IsTrackable (X : Asm 𝓤) (Y : Asm 𝓤) (f : ⟨ X ⟩ → ⟨ Y ⟩) : 𝓤 ̇ where 
  open AsmStr (str X) renaming (_⊩_ to _⊩x_)
  open AsmStr (str Y) renaming (_⊩_ to _⊩y_)
  field
    isTrackable : ∃[ r ∈ ⟨ A ⟩ ] ∀ (a : ⟨ A ⟩) (x : ⟨ X ⟩)
      → a ⊩x x → Σ[ p ∈ r · a ↓ ] value (r · a) p ⊩y f x

record Trackable (X : Asm 𝓤) (Y : Asm 𝓤) : 𝓤 ̇ where
  field
    fun         : ⟨ X ⟩ → ⟨ Y ⟩
    isTrackable : IsTrackable X Y fun
