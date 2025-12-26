# Decreasing sequences in posets

```agda
module order-theory.decreasing-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.propositions
open import foundation.universe-levels

open import order-theory.increasing-sequences-posets
open import order-theory.opposite-posets
open import order-theory.posets
open import order-theory.sequences-posets
```

</details>

## Idea

A [sequence](order-theory.sequences-posets.md) in a
[poset](order-theory.posets.md) is
{{#concept "decreasing" Disambiguation="sequence in a poset" Agda=is-decreasing-sequence-Poset}}
if it is [increasing](order-theory.increasing-sequences-posets.md) in the
[opposite poset](order-theory.opposite-posets.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-decreasing-prop-sequence-Poset : sequence-type-Poset P → Prop l2
  is-decreasing-prop-sequence-Poset =
    is-increasing-prop-sequence-Poset (opposite-Poset P)

  is-decreasing-sequence-Poset : sequence-type-Poset P → UU l2
  is-decreasing-sequence-Poset u =
    type-Prop (is-decreasing-prop-sequence-Poset u)
```

## Properties

### A sequence `u` in a poset is decreasing if and only if `uₙ₊₁ ≤ uₙ` for all `n : ℕ`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u : sequence-type-Poset P)
  where

  abstract
    is-decreasing-leq-succ-sequence-Poset :
      ((n : ℕ) → leq-Poset P (u (succ-ℕ n)) (u n)) →
      is-decreasing-sequence-Poset P u
    is-decreasing-leq-succ-sequence-Poset =
      is-increasing-leq-succ-sequence-Poset (opposite-Poset P) u

    leq-succ-is-decreasing-sequence-Poset :
      is-decreasing-sequence-Poset P u →
      ((n : ℕ) → leq-Poset P (u (succ-ℕ n)) (u n))
    leq-succ-is-decreasing-sequence-Poset =
      leq-succ-is-increasing-sequence-Poset (opposite-Poset P) u
```
