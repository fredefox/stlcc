module Stlcc.Variables where

open import Stlcc.Types
open import Stlcc.Contexts

data _⊢_ : Ctxt → Type → Set where
  zero : {Γ : Ctxt} {A : Type}
    → (A ∷ Γ) ⊢ A
  succ : {Γ : Ctxt} {A B : Type}
    → Γ ⊢ A → (B ∷ Γ) ⊢ A
