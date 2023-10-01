# Modal logic syntax

```agda
module modal-logic.modal-logic-syntax where
```

<details><summary>Imports</summary>

```agda
-- open import foundation.contractible-types
-- open import foundation.dependent-pair-types
-- open import foundation.equivalences
-- open import foundation.identity-types
-- open import foundation.propositions
-- open import foundation.sets
open import foundation.booleans
open import foundation.binary-relations
open import foundation.decidable-types
open import foundation.sets
open import foundation.powersets
open import foundation-core.propositions
open import foundation.universe-levels
open import foundation.unit-type

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
valuate-cl v (var x) = v x
valuate-cl v ⊥ = false
valuate-cl v (a ⇒ b) = implication-bool (valuate-cl v a) (valuate-cl v b)
valuate-cl v (□ _) = false

tautology : formula → UU lzero
tautology a = ∀ v → type-prop-bool (valuate-cl v a)
```

**Examples**

```agda
module tautology-example where
  A = var 0
  B = var 1
  C = var 2

  ex1 : tautology ⊤
  ex1 v = star

  ex2 : ¬ (tautology ⊥)
  ex2 h = h (λ _ → false)

  ex3 : tautology (A ⇒ A)
  ex3 v with v 0
  ... | true  = star
  ... | false = star

  ex4 : tautology ((A ⇒ B) ∨ (B ⇒ A))
  ex4 v with v 0 | v 1
  ... | true  | true  = star
  ... | true  | false = star
  ... | false | true  = star
  ... | false | false = star

  ex5 : tautology ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))
  ex5 v with v 0 | v 1 | v 2
  ... | true  | true  | true  = star
  ... | true  | true  | false = star
  ... | true  | false | true  = star
  ... | true  | false | false = star
  ... | false | true  | true  = star
  ... | false | true  | false = star
  ... | false | false | true  = star
  ... | false | false | false = star

  ex6 : ¬ (tautology A)
  ex6 h = h (λ _ → false)
```

**Tautology is decidable**

```agda
is-decidable-tautology : (a : formula) → is-decidable (tautology a)
is-decidable-tautology (var x) = inr (λ h → h (λ _ → false))
is-decidable-tautology ⊥ = inr (λ h → h (λ _ → false))
is-decidable-tautology (a ⇒ b) = {!   !}
is-decidable-tautology (□ a) = inr (λ h → h (λ _ → false))
```

**Semantics**

```agda
data ⊢_ : formula → UU lzero where
  ax : {a : formula} → tautology a → ⊢ a
  mp : {a b : formula} → ⊢ (a ⇒ b) → ⊢ a → ⊢ b
  nec : {a : formula} → ⊢ (□ a) → ⊢ a

record kripke-frame {l : Level} (w : UU l) : UU (lsuc l) where
  constructor frame
  field
    R : Relation l w

open kripke-frame public

module sets where
  module _
    {l1 : Level}
    (l2 : Level)
    (w : UU l1)
    where

    private
      l = lsuc (l1 ⊔ lsuc l2)
      W = powerset l2 w

    record kripke-model : UU l where
      constructor model
      field
        f : kripke-frame w
        V : ℕ → W
    open kripke-model public

  module _
    {l1 l2 : Level}
    {w : UU l1}
    where

    private
      l = lsuc (l1 ⊔ lsuc l2)

    data _,_⊨_ (M : kripke-model l2 w) (x : w) : formula → UU l where
      ⊨-var : {n : ℕ} → is-in-subtype (V M n) x → M , x ⊨ (var n)
      ⊨-left̄⇒ : {a b : formula} → M , x ⊨ (~ a) → M , x ⊨ (a ⇒ b) -- strict positivity
      ⊨-right⇒ : {a b : formula} → M , x ⊨ b → M , x ⊨ (a ⇒ b)
    open _,_⊨_ public

    _,_⊭_ : kripke-model l2 w → w → formula → UU l
    M , x ⊭ a = ¬ (M , x ⊨ a)

    _⊨M_ : kripke-model l2 w → formula → UU l
    M ⊨M a = (x : w) → M , x ⊨ a

    _⊭M_ : kripke-model l2 w → formula → UU l
    M ⊭M a = ¬ (M ⊨M a)

  module _
    {l : Level}
    (w : UU l)
    where

    _⊨F_ : kripke-frame w → formula → UUω
    F ⊨F a = (l2 : Level) (M : kripke-model l2 w) → (M ⊨M a)

    -- _⊭F_ : kripke-frame w → formula → UUω
    -- F ⊭F a = ¬ (F ⊨F a) -- Why I cannot write this?


module functions where
  module _
    {l : Level}
    (w : UU l)
    where

    private
    -- bool or type?

      -- in-subset : {l : Level} → UU l → UU l
      -- in-subset A = A → bool

      in-subset : {l : Level} → UU l → UU (l ⊔ lsuc lzero)
      in-subset A = A → UU lzero

    record kripke-model : UU (lsuc l) where
      constructor model
      field
        F : kripke-frame w
        V : ℕ → in-subset w
    open kripke-model public

    data _,_⊨_ (M : kripke-model) (x : w) : formula → UU l where
      ⊨-var : {n : ℕ} → V M n x → M , x ⊨ (var n)
      ⊨-left̄⇒ : {a b : formula} → M , x ⊨ (~ a) → M , x ⊨ (a ⇒ b) -- strict positivity
      ⊨-right⇒ : {a b : formula} → M , x ⊨ b → M , x ⊨ (a ⇒ b)
    open _,_⊨_ public

    _,_⊭_ : kripke-model → w → formula → UU l
    M , x ⊭ a = ¬ (M , x ⊨ a)

    _⊨M_ : kripke-model → formula → UU l
    M ⊨M a = ∀ x → M , x ⊨ a

    _⊭M_ : kripke-model → formula → UU l
    M ⊭M a = ¬ (M ⊨M a)

    _⊨F_ : kripke-frame w → formula → UU (l ⊔ lsuc lzero)
    F ⊨F a = ∀ V → model F V ⊨M a

    _⊭F_ : kripke-frame w → formula → UU (l ⊔ lsuc lzero)
    F ⊭F a = ¬ (F ⊨F a)

    _⊨C_ : in-subset (kripke-frame w) → formula → UU (lsuc l)
    C ⊨C a = ∀ F → C F → F ⊨F a

    _⊭C_ : in-subset (kripke-frame w) → formula → UU (lsuc l)
    C ⊭C a = ¬ (C ⊨C a)
```
