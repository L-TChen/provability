module Calculus.Untyped.Progress where

open import Prelude
  hiding (_∘_)
open import Calculus.Untyped.Base

private
  variable
    m n l          : ℕ
    M N L M′ N′ L′ : Λ n

infix  8  ′_
------------------------------------------------------------------------------
-- Normal terms

data Neutral {n : ℕ} : Λ n → 𝓤₀ ̇
data Normal  {n : ℕ} : Λ n → 𝓤₀ ̇

data Neutral {n} where
  `_  : (x : Fin n)
      -------------
    → Neutral (` x)
  _·_
    : Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)

data Normal where
  ′_
    : Neutral M
      ---------
    → Normal M
  ƛ_
    : Normal N
      ------------
    → Normal (ƛ N)

neutral-does-not-reduce : Neutral M → M -→ N → ⊥
normal-does-not-reduce  : Normal M → M -→ N → ⊥

neutral-does-not-reduce (` x) ()
neutral-does-not-reduce (M · N) (ξₗ M-→N) = neutral-does-not-reduce M M-→N
neutral-does-not-reduce (M · N) (ξᵣ M-→N) = normal-does-not-reduce N M-→N

normal-does-not-reduce (′ M) M-→N     = neutral-does-not-reduce M M-→N
normal-does-not-reduce (ƛ M) (ζ M-→N) = normal-does-not-reduce M M-→N

------------------------------------------------------------------------------
-- Progress theorem i.e. one-step evaluator

data Progress (M : Λ n) : 𝓤₀ ̇ where
  step
    : M -→ N
      ----------
    → Progress M

  done
    : Normal M
    → Progress M

progress : (M : Λ n) → Progress M
progress (` x)                                 =  done (′ ` x )
progress (ƛ N)  with  progress N
... | step N—→N′                               =  step (ζ N—→N′)
... | done NrmN                                =  done (ƛ NrmN)
progress (` x · M) with progress M
... | step M—→M′                               =  step (ξᵣ M—→M′)
... | done NrmM                                =  done (′ (` x) · NrmM)
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L—→L′                               =  step (ξₗ L—→L′)
... | done (′ NeuL) with progress M
...    | step M—→M′                            =  step (ξᵣ M—→M′)
...    | done NrmM                             =  done (′ NeuL · NrmM)

