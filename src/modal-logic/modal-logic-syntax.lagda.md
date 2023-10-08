# Modal logic syntax

```agda
module modal-logic.modal-logic-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-negation
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

LEM : (l : Level) → UU (lsuc l)
LEM l = (T : UU l) → is-decidable T

-- bool or type?
in-subset : {l : Level} → UU l → UU l
in-subset A = A → bool

-- in-subset : {l : Level} → UU l → UU (l ⊔ lsuc lzero)
-- in-subset A = A → UU lzero
```

**Syntax**

```agda
module _
  {l : Level}
  (i : UU l)
  where

  data formula : UU l where
    var : i → formula
    ⊥ : formula
    _⇒_ : formula → formula → formula
    □ : formula → formula

module _
  {l : Level}
  {i : UU l}
  where

  ~ : formula i → formula i
  ~ a = a ⇒ ⊥

  _∨_ : formula i → formula i → formula i
  a ∨ b = (~ a) ⇒ b

  _∧_ : formula i → formula i → formula i
  a ∧ b = ~ (a ⇒ (~ b))

  ⊤ : formula i
  ⊤ = ~ ⊥

  ◇ : formula i → formula i
  ◇ a = ~ (□ (~ a))

  data ⊢ : formula i → UU l where
    ax-k : {a b : formula i} → ⊢ (a ⇒ (b ⇒ a))
    ax-s : {a b c : formula i} → ⊢ ((a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c)))
    ax-dn : {a : formula i} → ⊢ ((~ (~ a)) ⇒ a)
    ax-n : {a b : formula i} → ⊢ ((□ (a ⇒ b)) ⇒ ((□ a) ⇒ (□ b)))
    mp : {a b : formula i} → ⊢ (a ⇒ b) → ⊢ a → ⊢ b
    nec : {a : formula i} → ⊢ a → ⊢ (□ a)
```

**Semantics**

```agda
module _
  {l1 : Level}
  (w : UU l1)
  where

  record kripke-frame : UU (lsuc l1) where
    constructor frame
    field
      R : Relation l1 w

  open kripke-frame public

  module _
    {l2 : Level}
    (i : UU l2)
    where

    private
      l = l1 ⊔ l2

    record kripke-model : UU (lsuc l) where
      constructor model
      field
        F : kripke-frame
        V : i → in-subset w

    open kripke-model public

    _,_⊨_ : kripke-model → w → formula i → UU l
    M , x ⊨ var n = Lift _ (type-prop-bool (V M n x))
    M , x ⊨ ⊥ = Lift _ empty
    M , x ⊨ (a ⇒ b) = ¬ (M , x ⊨ a) + M , x ⊨ b
    M , x ⊨ (□ a) = ∀ y → R (F M) x y → M , y ⊨ a

    _,_⊭_ : kripke-model → w → formula i → UU l
    M , x ⊭ a = ¬ (M , x ⊨ a)

    _⊨M_ : kripke-model → formula i → UU l
    M ⊨M a = ∀ x → M , x ⊨ a

    _⊭M_ : kripke-model → formula i → UU l
    M ⊭M a = ¬ (M ⊨M a)

    _⊨F_ : kripke-frame → formula i → UU l
    F ⊨F a = ∀ V → model F V ⊨M a

    _⊭F_ : kripke-frame → formula i → UU l
    F ⊭F a = ¬ (F ⊨F a)

    _⊨C_ : in-subset kripke-frame → formula i → UU (lsuc l1 ⊔ l2)
    C ⊨C a = ∀ F → type-prop-bool (C F) → F ⊨F a

    _⊭C_ : in-subset kripke-frame → formula i → UU (lsuc l1 ⊔ l2)
    C ⊭C a = ¬ (C ⊨C a)
```

**Soundness**

```agda
    all-frames : in-subset kripke-frame
    all-frames = λ _ → true

    is-classical : kripke-model → UU l
    is-classical M = ∀ a x → is-decidable (M , x ⊨ a)

    imp-force : {a b : formula i} {M : kripke-model} {x : w}
              → M , x ⊨ (a ⇒ b)
              → M , x ⊨ a
              → M , x ⊨ b
    imp-force (inl fab) fa = ex-falso (fab fa)
    imp-force (inr fab) fa = fab

    soundness : {a : formula i}
              → ⊢ a
              → (M : kripke-model)
              → is-classical M
              → M ⊨M a
    soundness (mp dab da) M dec x with soundness dab M dec x
    ... | inl f = ex-falso (f (soundness da M dec x))
    ... | inr f = f
    soundness {a ⇒ (b ⇒ a)} ax-k M dec x with dec a x
    ... | inl fna = inr (inr fna)
    ... | inr fa = inl fa
    soundness {abc ⇒ (ab ⇒ ac)} ax-s M dec x with dec abc x
    ... | inr fabc = inl fabc
    ... | inl (inl fna) = inr (inr (inl fna))
    ... | inl (inr (inr fc)) = inr (inr (inr fc))
    ... | inl (inr (inl fnb)) with dec ab x
    ...   | inr fab = inr (inl fab)
    ...   | inl (inl fna) = inr (inr (inl fna))
    ...   | inl (inr fb) = ex-falso (fnb fb)
    soundness {((a ⇒ ⊥) ⇒ ⊥) ⇒ a} ax-dn M dec x with dec a x
    ... | inl fa = inr fa
    ... | inr fna with dec (~ (~ a)) x
    ...   | inl (inl fnna) = ex-falso (fnna (inl fna))
    ...   | inr fnnna = inl (fnnna)
    soundness {ab ⇒ (a ⇒ b)} ax-n M dec x with dec ab x
    ... | inr fab = inl fab
    ... | inl fab with dec a x
    ...   | inr fa = inr (inl fa)
    ...   | inl fa = inr (inr (λ y r → imp-force (fab y r) (fa y r)))
    soundness (nec d) M dec x y _ = soundness d M dec y

    soundness-LEM : {a : formula i}
                  → LEM l
                  → ⊢ a
                  → (M : kripke-model)
                  → M ⊨M a
    soundness-LEM lem d M = soundness d M (λ b x → lem _)
```
