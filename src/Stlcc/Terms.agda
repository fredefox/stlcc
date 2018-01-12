module Stlcc.Terms where

open import Stlcc.Types
open import Stlcc.Contexts hiding (tabulate)
import Stlcc.Variables
module V = Stlcc.Variables

infixl 5 _⊢_
mutual
  -- Well-typed terms with explicit substitutions
  data _⊢_ : Ctxt → Type → Set where
    𝟙   : {Γ : Ctxt} → Γ ⊢ 𝟙
    var : {Γ : Ctxt} {A : Type}
      → Γ V.⊢ A → Γ ⊢ A
    abs : {Γ : Ctxt} {A B : Type}
      → (A ∷ Γ) ⊢ B → Γ ⊢ A ⇒ B
    app : {Γ : Ctxt} {A B : Type}
      → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    subst : {Γ Δ : Ctxt} {A : Type}
      → Sub Γ Δ → Δ ⊢ A → Γ ⊢ A

  -- Substitutions
  data Sub : Ctxt → Ctxt → Set where
    [] : {Γ : Ctxt} → Sub Γ []
    _∷_ : {A : Type} → {Γ Δ : Ctxt}
      → Γ ⊢ A → Sub Γ Δ → Sub Γ (A ∷ Δ)

lookup : ∀ {Γ Δ A} → Δ V.⊢ A → Sub Γ Δ → Γ ⊢ A
lookup V.zero (t ∷ _) = t
lookup (V.succ n) (_ ∷ δ) = lookup n δ

tabulate : ∀ {Γ Δ} → ((A : Type) → Δ V.⊢ A → Γ ⊢ A) → Sub Γ Δ
tabulate {Δ = []} f = []
tabulate {Δ = B ∷ Δ} f = f B V.zero ∷ tabulate λ A x → f A (V.succ x)

wk : ∀ {Γ A} → Sub (A ∷ Γ) Γ
wk {Γ} = tabulate λ B x → var (V.succ x)

_∘_ : ∀ {Δ Γ Ξ} → Sub Ξ Δ → Sub Δ Γ → Sub Ξ Γ
_ ∘ [] = []
δ ∘ (t ∷ ρ) = subst δ t ∷ (δ ∘ ρ)

lift ⇑ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {A} → Sub (A ∷ Γ) (A ∷ Δ)
lift δ = var V.zero ∷ (wk ∘ δ)
⇑ = lift

id : (Γ : Ctxt) → Sub Γ Γ
id [] = []
id (x ∷ Γ) = var V.zero ∷ wk

module JudgementalEquality where
  open import Relation.Binary.Core hiding (_⇒_)

  infixl 4 _≅_
  data _≅_  : {Γ : Ctxt} → {T : Type} → Γ ⊢ T → Γ ⊢ T → Set where
    β-eqv : {Γ : Ctxt} {A B : Type} {t : (A ∷ Γ) ⊢ B} {u : Γ ⊢ A}
      → app (abs t) u ≅ subst (u ∷ id Γ) t
    η-eqv : {Γ : Ctxt} {A B : Type} {f : Γ ⊢ A ⇒ B} -- {u : Γ ⊢ A}
      → f ≅ abs (app (subst wk f) (var V.zero))
    η-eqv-subst : {Γ Δ : Ctxt} {A : Type} {t : Γ ⊢ A} {δ : Sub Γ Δ}
      → subst (t ∷ δ) (var V.zero) ≅ t
    -- Not mentioned in Abel's solution.
    -- subst-prop-var : ∀ {Γ Δ} {δ : Sub Γ Δ} {A}   {x : Δ V.⊢ A}
    --   → subst δ (var x) ≅ lookup x δ
    subst-prop-abs : ∀ {Γ Δ} {δ : Sub Γ Δ} {A B} {t : (A ∷ Δ) ⊢ B}
      → subst δ (abs t) ≅ abs (subst (⇑ δ) t)
    subst-prop-app : ∀ {Γ Δ} {δ : Sub Γ Δ} {A B} {f : Δ ⊢ A ⇒ B} {t : Δ ⊢ A}
      → subst δ (app f t) ≅ app (subst δ f) (subst δ t)
    isReflexive  : ∀ {Γ T} → Reflexive  {A = Γ ⊢ T} _≅_
    isSymmetric  : ∀ {Γ T} → Symmetric  {A = Γ ⊢ T} _≅_
    isTransitive : ∀ {Γ T} → Transitive {A = Γ ⊢ T} _≅_

  data _≈_ : ∀ {Γ Δ Γ' Δ'} → Sub Δ Γ → Sub Δ' Γ' → Set where
