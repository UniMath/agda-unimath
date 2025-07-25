# Increasing sequences in partially ordered sets

```agda
module order-theory.increasing-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.sequences-posets
open import order-theory.subposets
```

</details>

## Idea

A [sequence in a partially ordered set](order-theory.sequences-posets.md) `u` is
{{#concept "increasing" Disambiguation="sequence in a poset" Agda=is-increasing-sequence-Poset}}
if it [preserves](order-theory.order-preserving-maps-posets.md) the
[standard ordering on the natural numbers](elementary-number-theory.inequality-natural-numbers.md)
or, equivalently, if `uₙ ≤ uₙ₊₁` for all `n : ℕ`.

## Definitions

### The predicate of being an increasing sequence in a partially ordered set

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-type-Poset P)
  where

  is-increasing-prop-sequence-Poset : Prop l2
  is-increasing-prop-sequence-Poset =
    preserves-order-prop-Poset ℕ-Poset P u

  is-increasing-sequence-Poset : UU l2
  is-increasing-sequence-Poset =
    type-Prop is-increasing-prop-sequence-Poset
```

### The poset of increasing sequences in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  poset-increasing-sequence-Poset : Poset (l1 ⊔ l2) l2
  poset-increasing-sequence-Poset =
    poset-Subposet
      ( sequence-Poset P)
      ( is-increasing-prop-sequence-Poset P)

  increasing-sequence-Poset : UU (l1 ⊔ l2)
  increasing-sequence-Poset =
    type-Poset poset-increasing-sequence-Poset

  seq-increasing-sequence-Poset :
    increasing-sequence-Poset →
    sequence-type-Poset P
  seq-increasing-sequence-Poset = pr1

  is-increasing-seq-increasing-sequence-Poset :
    (u : increasing-sequence-Poset) →
    is-increasing-sequence-Poset
      ( P)
      ( seq-increasing-sequence-Poset u)
  is-increasing-seq-increasing-sequence-Poset = pr2
```

## Properties

### A sequence `u` in a poset is increasing if and only if `uₙ ≤ uₙ₊₁` for all `n : ℕ`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-type-Poset P)
  where

  is-increasing-leq-succ-sequence-Poset :
    ((n : ℕ) → leq-Poset P (u n) (u (succ-ℕ n))) →
    is-increasing-sequence-Poset P u
  is-increasing-leq-succ-sequence-Poset =
    preserves-order-ind-ℕ-Poset P u

  leq-succ-is-increasing-sequence-Poset :
    is-increasing-sequence-Poset P u →
    ((n : ℕ) → leq-Poset P (u n) (u (succ-ℕ n)))
  leq-succ-is-increasing-sequence-Poset H n =
    H n (succ-ℕ n) (succ-leq-ℕ n)
```
