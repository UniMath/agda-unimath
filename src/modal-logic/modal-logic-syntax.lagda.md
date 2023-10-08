# Modal logic syntax

```agda
module modal-logic.modal-logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.booleans
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.powersets
open import foundation.universe-levels
open import foundation.unit-type
open import foundation.action-on-identifications-functions
open import foundation.logical-equivalences

open import foundation-core.transport-along-identifications
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.negation
open import foundation-core.identity-types

open import elementary-number-theory.natural-numbers
```

</details>

## Idea

TODO

## Definition

```agda
-- I'am not found in lib
record Lift {a : Level} (l : Level) (A : UU a) : UU (a ⊔ l) where
  constructor lift
  field lower : A
open Lift

is-decidable-type-prop-bool : (b : bool) → is-decidable (type-prop-bool b)
is-decidable-type-prop-bool true = inl star
is-decidable-type-prop-bool false = inr (λ ())
```

**Syntax**

```agda
data formula : UU lzero where
  var : ℕ → formula
  ⊥ : formula
  _⇒_ : formula → formula → formula
  □_ : formula → formula

~_ : formula → formula
~ a = a ⇒ ⊥

_∨_ : formula → formula → formula
a ∨ b = (~ a) ⇒ b

_∧_ : formula → formula → formula
a ∧ b = ~ (a ⇒ (~ b))

⊤ : formula
⊤ = ~ ⊥

◇_ : formula → formula
◇ a = ~ (□ (~ a))
```

**Tautology**

```agda
valuate-cl : (ℕ → bool) → formula → bool
valuate-cl v (var n) = v n
valuate-cl v ⊥ = false
valuate-cl v (a ⇒ b) = implication-bool (valuate-cl v a) (valuate-cl v b)
valuate-cl v (□ _) = false

data without-boxes : formula → UU lzero where
  without-boxes-var : (n : ℕ) → without-boxes (var n)
  without-boxes-bot : without-boxes ⊥
  without-boxes-imp : {a b : formula} →
                      without-boxes a →
                      without-boxes b →
                      without-boxes (a ⇒ b)

tautology : formula → UU lzero
tautology a = without-boxes a × ∀ v → type-prop-bool (valuate-cl v a)
```

**Examples**

```agda
module tautology-example where
  A = var 0
  B = var 1
  C = var 2

  ex1 : tautology ⊤
  ex1 = wb , λ _ → star
    where
    wb : without-boxes ⊤
    wb = without-boxes-imp without-boxes-bot without-boxes-bot

  ex2 : ¬ (tautology ⊥)
  ex2 h = pr2 h λ _ → false

  ex3 : tautology (A ⇒ A)
  ex3 = wb , val
    where
    wb : without-boxes (A ⇒ A)
    wb = (without-boxes-imp (without-boxes-var 0) (without-boxes-var 0))
    val : ∀ v → type-prop-bool (valuate-cl v (A ⇒ A))
    val v with v 0
    ... | true = star
    ... | false = star

  ex4 : tautology ((A ⇒ B) ∨ (B ⇒ A))
  ex4 = wb , val
    where
    wb : without-boxes ((A ⇒ B) ∨ (B ⇒ A))
    wb = without-boxes-imp
          (without-boxes-imp
            (without-boxes-imp (without-boxes-var 0) (without-boxes-var 1))
            without-boxes-bot)
          (without-boxes-imp (without-boxes-var 1) (without-boxes-var 0))
    val : ∀ v → type-prop-bool (valuate-cl v ((A ⇒ B) ∨ (B ⇒ A)))
    val v with v 0 | v 1
    ... | true  | true  = star
    ... | true  | false = star
    ... | false | true  = star
    ... | false | false = star

  ex5 : tautology ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))
  ex5 = wb , val
    where
    wb : without-boxes ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))
    wb = without-boxes-imp
          (without-boxes-imp
            (without-boxes-var 0)
            (without-boxes-var 1))
          (without-boxes-imp
            (without-boxes-imp
              (without-boxes-var 1)
              (without-boxes-var 2))
            (without-boxes-imp
              (without-boxes-var 0)
              (without-boxes-var 2)))
    val : ∀ v → type-prop-bool (valuate-cl v ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C))))
    val v with v 0 | v 1 | v 2
    ... | true  | true  | true  = star
    ... | true  | true  | false = star
    ... | true  | false | true  = star
    ... | true  | false | false = star
    ... | false | true  | true  = star
    ... | false | true  | false = star
    ... | false | false | true  = star
    ... | false | false | false = star

  ex6 : ¬ (tautology A)
  ex6 h = pr2 h (λ _ → false)

  ex7 : ¬ (tautology (⊥ ⇒ (□ A)))
  ex7 (without-boxes-imp _ () , _)
```

**Tautology is decidable**

```agda
without-boxes-inversion : {a b : formula} →
                          without-boxes (a ⇒ b) →
                          without-boxes a × without-boxes b
without-boxes-inversion (without-boxes-imp wa wb) = wa , wb

is-decidable-without-boxes : (a : formula) → is-decidable (without-boxes a)
is-decidable-without-boxes (var n) = inl (without-boxes-var n)
is-decidable-without-boxes ⊥ = inl without-boxes-bot
is-decidable-without-boxes (a ⇒ b)
  with is-decidable-without-boxes a | is-decidable-without-boxes b
... | inr wa | _ = inr λ w → wa (pr1 (without-boxes-inversion w))
... | inl wa | inr wb = inr λ w → wb (pr2 (without-boxes-inversion w))
... | inl wa | inl wb = inl (without-boxes-imp wa wb)
is-decidable-without-boxes (□ a) = inr (λ ())

is-decidable-tautology-v : (a : formula) → is-decidable (∀ v → type-prop-bool (valuate-cl v a))
is-decidable-tautology-v (var x) = inr λ h → h (λ _ → false)
is-decidable-tautology-v ⊥ = inr λ h → h (λ _ → false)
is-decidable-tautology-v (a ⇒ b) = {!   !}
is-decidable-tautology-v (□ a) = inr λ h → h (λ _ → false)

is-decidable-tautology : (a : formula) → is-decidable (tautology a)
is-decidable-tautology a
  with is-decidable-without-boxes a | is-decidable-tautology-v a
... | inr wa | _ = inr (λ x → wa (pr1 x))
... | inl wa | inr t = inr (λ x → t (pr2 x))
... | inl wa | inl t = inl (wa , t)
```

**Semantics**

```agda
data ⊢_ : formula → UU lzero where
  ax : {a : formula} → tautology a → ⊢ a
  k : {a b : formula} → ⊢ ((□ (a ⇒ b)) ⇒ ((□ a) ⇒ (□ b)))
  mp : {a b : formula} → ⊢ (a ⇒ b) → ⊢ a → ⊢ b
  nec : {a : formula} → ⊢ a → ⊢ (□ a)

record kripke-frame {l : Level} (w : UU l) : UU (lsuc l) where
  constructor frame
  field
    R : Relation l w

open kripke-frame public

private
-- bool or type?

  in-subset : {l : Level} → UU l → UU l
  in-subset A = A → bool

  -- in-subset : {l : Level} → UU l → UU (l ⊔ lsuc lzero)
  -- in-subset A = A → UU lzero

module _
  {l : Level}
  (w : UU l)
  -- (w : UU lzero)
  where

  record kripke-model : UU (lsuc l) where
  -- record kripke-model : UU₁ where
    constructor model
    field
      F : kripke-frame w
      V : ℕ → in-subset w
  open kripke-model public

  _,_⊨_ : kripke-model → w → formula → UU l
  M , x ⊨ var n = Lift _ (type-prop-bool (V M n x))
  M , x ⊨ ⊥ = Lift _ empty
  M , x ⊨ (a ⇒ b) = ¬ (M , x ⊨ a) + M , x ⊨ b
  M , x ⊨ (□ a) = ∀ y → R (F M) x y → M , y ⊨ a

  _,_⊭_ : kripke-model → w → formula → UU l
  M , x ⊭ a = ¬ (M , x ⊨ a)

  _⊨M_ : kripke-model → formula → UU l
  M ⊨M a = ∀ x → M , x ⊨ a

  _⊭M_ : kripke-model → formula → UU l
  M ⊭M a = ¬ (M ⊨M a)

  _⊨F_ : kripke-frame w → formula → UU l
  F ⊨F a = ∀ V → model F V ⊨M a

  _⊭F_ : kripke-frame w → formula → UU l
  F ⊭F a = ¬ (F ⊨F a)

  _⊨C_ : in-subset (kripke-frame w) → formula → UU (lsuc l)
  C ⊨C a = ∀ F → type-prop-bool (C F) → F ⊨F a

  _⊭C_ : in-subset (kripke-frame w) → formula → UU (lsuc l)
  C ⊭C a = ¬ (C ⊨C a)
```

**Force without boxes**

```agda
  force-without-boxes : {a : formula}
                      → without-boxes a
                      → {M : kripke-model}
                      → (x : w)
                      → type-prop-bool (valuate-cl (λ n → V M n x) a) ↔ M , x ⊨ a
  force-without-boxes (without-boxes-var n) x = (λ val → lift val) , λ f → lower f
  force-without-boxes without-boxes-bot x = (λ ()) , (λ ())
  force-without-boxes ab@{a ⇒ b} (without-boxes-imp wa wb) {M} x = prove→ , prove←
    where
    v = λ n → V M n x

    prove→ : type-prop-bool (valuate-cl v ab) → M , x ⊨ ab
    prove→ val with valuate-cl v a in eqa | valuate-cl v b in eqb
    ... | _ | true = inr (pr1 (force-without-boxes wb x) (tr type-prop-bool (inv eqb) _))
    ... | false | false = inl λ fa → tr type-prop-bool eqa (pr2 (force-without-boxes wa x) fa)

    prove← : M , x ⊨ ab → type-prop-bool (valuate-cl v ab)
    prove← (inl fab) = {!   !}
    prove← (inr fab) with pr2 (force-without-boxes wb x) fab in eqt
    ... | ttt = {!  ttt !}
  -- force-without-boxes (without-boxes-var n) x val = lift val
  -- force-without-boxes {a ⇒ b} (without-boxes-imp wa wb) {M} x val with valuate-cl (λ n → V M n x) a in eqa | valuate-cl (λ n → V M n x) b in eqb
  -- ... | true | true = inr (force-without-boxes wb x (tr type-prop-bool (inv eqb) val))
  -- ... | false | _ = inl {!   !} -- inl (λ fa → tr type-prop-bool eqa {! force-without-boxes  !})
```

**Soundness**

```agda
  -- all-frames : in-subset (kripke-frame w)
  -- all-frames = λ _ → true

  is-classical : kripke-model → UU l
  is-classical M = ∀ a x → is-decidable (M , x ⊨ a)

  imp-force : {a b : formula} {M : kripke-model} {x : w}
            → M , x ⊨ (a ⇒ b)
            → M , x ⊨ a
            → M , x ⊨ b
  imp-force (inl fab) fa = ex-falso (fab fa)
  imp-force (inr fab) fa = fab

  tautology-canonical : {a : formula}
                      → tautology a
                      → (M : kripke-model)
                      → M ⊨M a
  tautology-canonical {var n} (_ , t) M x = ex-falso (t (λ _ → false))
  tautology-canonical {⊥} (_ , t) M x = ex-falso (t (λ _ → false))
  tautology-canonical {a ⇒ b} (without-boxes-imp wa wb , t) M x =
    {!  !}
  tautology-canonical {□ a} () M x

  soundness : {a : formula}
            → ⊢ a
            → (M : kripke-model)
            → is-classical M
            → M ⊨M a
  soundness (mp dab da) M dec x with soundness dab M dec x
  ... | inl f = ex-falso (f (soundness da M dec x))
  ... | inr f = f
  soundness (ax t) M dec = {!   !}
  soundness {ab ⇒ (a ⇒ b)} k M dec x with dec ab x
  ... | inr fab = inl fab
  ... | inl fab with dec a x
  ...   | inr fa = inr (inl fa)
  ...   | inl fa = inr (inr (λ y r → imp-force (fab y r) (fa y r)))
  soundness (nec d) M dec x y _ = soundness d M dec y

  -- soundness : {a : formula} → ⊢ a → all-frames ⊨C a
  -- soundness {a} (mp dab da) F _ V x with soundness dab F star V x
  -- ... | inl d = ex-falso (d (soundness da F star V x))
  -- ... | inr d = d
  -- soundness {a} (ax t) = tautology-canonical t
  -- -- soundness {var n} (ax (_ , t)) = ex-falso (t λ _ → false)
  -- -- soundness {⊥} (ax (_ , t)) = ex-falso (t λ _ → false)
  -- -- soundness {a ⇒ b} (ax (without-boxes-imp wa wb , t)) F _ V x
  -- --   = {!  !}
  -- soundness {(□ (a ⇒ b)) ⇒ ((□ a) ⇒ (□ b))} k F _ V
  --   = {!   !}
  -- soundness {□ a} (nec d) F _ V x y _ = soundness d F star V y
```
