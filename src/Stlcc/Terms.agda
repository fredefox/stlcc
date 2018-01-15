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

_//_ : {Γ Δ : Ctxt} {A : Type}
  → Δ ⊢ A → Sub Γ Δ → Γ ⊢ A
t // δ = subst δ t

lookup : ∀ {Γ Δ A} → Δ V.⊢ A → Sub Γ Δ → Γ ⊢ A
lookup V.zero (t ∷ _) = t
lookup (V.succ n) (_ ∷ δ) = lookup n δ

tabulate : ∀ {Γ Δ} → ((A : Type) → Δ V.⊢ A → Γ ⊢ A) → Sub Γ Δ
tabulate {Δ = []} f = []
tabulate {Δ = B ∷ Δ} f = f B V.zero ∷ tabulate λ A x → f A (V.succ x)

incr : ∀ {Γ A B} → Γ V.⊢ A → (B ∷ Γ) ⊢ A
incr x = var (V.succ x)

wk : ∀ {Γ A} → Sub (A ∷ Γ) Γ
wk = tabulate λ _ → incr

_∘_ : ∀ {Δ Γ Ξ} → Sub Ξ Δ → Sub Δ Γ → Sub Ξ Γ
_ ∘ [] = []
ρ ∘ (t ∷ δ) = t // ρ ∷ (ρ ∘ δ)

_>>>_ : ∀ {Δ Γ Ξ} → Sub Δ Γ → Sub Ξ Δ → Sub Ξ Γ
δ >>> ρ = ρ ∘ δ

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
      → app (abs t) u ≅ t // (u ∷ id Γ)
    η-eqv : {Γ : Ctxt} {A B : Type} {f : Γ ⊢ A ⇒ B}
      → f ≅ abs (app (f // wk) (var V.zero))
    η-eqv-subst : {Γ Δ : Ctxt} {A : Type} {t : Γ ⊢ A} {δ : Sub Γ Δ}
      → var V.zero // (t ∷ δ) ≅ t
    -- Not mentioned in Abel's solution.
    -- subst-prop-var : ∀ {Γ Δ} {δ : Sub Γ Δ} {A}   {x : Δ V.⊢ A}
    --   → subst δ (var x) ≅ lookup x δ
    subst-prop-abs : ∀ {Γ Δ} {δ : Sub Γ Δ} {A B} {t : (A ∷ Δ) ⊢ B}
      → abs t // δ   ≅ abs (t // ⇑ δ )
    subst-prop-app : ∀ {Γ Δ} {δ : Sub Γ Δ} {A B} {f : Δ ⊢ A ⇒ B} {t : Δ ⊢ A}
      → app f t // δ ≅ app (f // δ) (t // δ)
    subst-prop-comp : ∀ {Δ Γ Ξ} {δ : Sub Γ Δ} {ρ : Sub Ξ Γ} {A} {t : Δ ⊢ A}
      → (t // δ) // ρ ≅ t // (ρ ∘ δ)
    isReflexive  : ∀ {Γ T} → Reflexive  {A = Γ ⊢ T} _≅_
    isSymmetric  : ∀ {Γ T} → Symmetric  {A = Γ ⊢ T} _≅_
    isTransitive : ∀ {Γ T} → Transitive {A = Γ ⊢ T} _≅_

  instance
    ≅-isEquivalence : ∀ {Γ T} → IsEquivalence {A = Γ ⊢ T} _≅_
    ≅-isEquivalence = record
      { refl = isReflexive ; sym = isSymmetric ; trans = isTransitive }

  subst-prop-var : ∀ {Γ Δ} {δ : Sub Γ Δ} {A} {x : Δ V.⊢ A}
    → var x // δ ≅ lookup x δ
  subst-prop-var {δ = x ∷ δ}  {x = V.zero} = η-eqv-subst
  subst-prop-var {δ = x₁ ∷ δ} {x = V.succ x} = {!subst-prop-var {δ = ?}!}

  data _≈_ : ∀ {Γ Δ} → Sub Δ Γ → Sub Δ Γ → Set where
    eq-terms : ∀ {Δ A Γ} → {t : Δ ⊢ A} {u : Δ ⊢ A} {δ : Sub Δ Γ} {ρ : Sub Δ Γ}
      → t ≅ u → δ ≈ ρ → (t ∷ δ) ≈ (u ∷ ρ)
    comp-wk : ∀ {Γ A Δ} {x : Γ ⊢ A} {δ : Sub Γ Δ}
      → ((x ∷ δ) ∘ wk) ≈ δ
    -- comp-wk : ((x ∷ δ) ∘ tabulate (λ B x₁ → var (V.succ x₁))) ≈ δ
    isReflexive  : ∀ {Γ Δ} → Reflexive  {A = Sub Γ Δ} _≈_
    isSymmetric  : ∀ {Γ Δ} → Symmetric  {A = Sub Γ Δ} _≈_
    isTransitive : ∀ {Γ Δ} → Transitive {A = Sub Γ Δ} _≈_

  incr2 : ∀ {Γ A B C} → Γ V.⊢ A → (C ∷ B ∷ Γ) ⊢ A
  incr2 x = var (V.succ (V.succ x))

  assoc : ∀ {Γ Δ Ξ Ψ} {δ : Sub Ψ Ξ} {ρ : Sub Ξ Δ} {σ : Sub Δ Γ} → ((δ ∘ ρ) ∘ σ) ≈ (δ ∘ (ρ ∘ σ))
  assoc = {!!}

  comp-wk' : ∀ {Γ A Δ} {x : Γ ⊢ A} {δ : Sub Γ Δ}
    → ((x ∷ δ) ∘ wk) ≈ δ
  comp-wk' {δ = []} = isReflexive
  comp-wk' {δ = x₁ ∷ δ} = eq-terms subst-prop-var lem
    where
--    wk : ∀ {Γ A} → Sub (A ∷ Γ) Γ
--    wk {Γ} = tabulate λ B x → var (V.succ x)
      lem : ∀ {Γ A Δ A₁} {x : Γ ⊢ A₁} {x₁ : Γ ⊢ A} {δ : Sub Γ Δ} →
--        ((x ∷ (x₁ ∷ δ)) ∘ tabulate (λ _ y → var (V.succ (V.succ y)))) ≈ δ
        ((x ∷ (x₁ ∷ δ)) ∘ tabulate (λ _ → incr2)) ≈ δ
      lem = {!!}
      lem2 : ∀ {Γ B T0 T1} → {x : Γ ⊢ B} → tabulate {Γ = T0 ∷ T1 ∷ Γ} (λ _ → incr2) ≈ (wk ∘ wk)
      lem2 = {!!}
      lem3 : ∀ {Γ A Δ A₁ B C} {x : Γ ⊢ A₁} {x₁ : Γ ⊢ A} {δ : Sub Γ (C ∷ B ∷ Δ)} →
        (δ ∘ tabulate (λ _ → incr2)) ≈ (δ ∘ (wk ∘ wk))
      lem3 = {!subst!}
      lem4 : ∀ {Γ Δ B C} {δ : Sub Γ (C ∷ B ∷ Δ)}
        → (δ ∘ (wk ∘ wk)) ≈ ((δ ∘ wk) ∘ wk)
      lem4 = isSymmetric assoc

  open import Relation.Binary
  open import Level

  instance
    ≈-isEquivalence : ∀ {Γ Δ} → IsEquivalence {A = Sub Γ Δ} _≈_
    ≈-isEquivalence = record
      { refl = isReflexive ; sym = isSymmetric ; trans = isTransitive }

  isSetoid : ∀ {Γ Δ} → Setoid zero zero
  isSetoid {Γ} {Δ} = record { Carrier = Sub Δ Γ ; _≈_ = _≈_ ; isEquivalence = ≈-isEquivalence }

  identity : ∀ {Γ Δ} → {δ : Sub Γ Δ} → (δ ∘ id Δ) ≈ δ
  identity {δ = []} = isReflexive
  -- ((x ∷ δ) ∘ id (? ∷ ?)) ≈ (x ∷ δ)
  identity {Γ} {Δ} {δ = x ∷ δ} = eq-terms subst-prop-var comp-wk
    where
      open import Relation.Binary.PreorderReasoning
        (Setoid.preorder (isSetoid {Γ} {Δ}))
