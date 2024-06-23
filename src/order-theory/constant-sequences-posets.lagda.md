# Constant sequences in partially ordered sets

```agda
module order-theory.constant-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import foundation.constant-sequences
open import foundation.coproduct-types
open import foundation.universe-levels

open import order-theory.decreasing-sequences-posets
open import order-theory.increasing-sequences-posets
open import order-theory.posets
open import order-theory.sequences-posets
```

</details>

## Idea

A [sequence in a partially ordered set](order-theory.sequences-posets.md) is
[constant](foundation.constant-sequences.md) if it is both
[increasing](order-theory.increasing-sequences-posets.md) and
[decreasing](order-theory.decreasing-sequences-posets.md).

## Properties

### A sequence in a partially ordered set is constant if and only if it is both increasing and decreasing

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) {u : sequence-poset P}
  where

  increasing-is-constant-sequence-poset :
    is-constant-sequence u → is-increasing-sequence-poset P u
  increasing-is-constant-sequence-poset H p q I = leq-eq-Poset P (H p q)

  decreasing-is-constant-sequence-poset :
    is-constant-sequence u → is-decreasing-sequence-poset P u
  decreasing-is-constant-sequence-poset H p q I = leq-eq-Poset P (H q p)

  constant-is-increasing-decreasing-sequence-poset :
    is-increasing-sequence-poset P u →
    is-decreasing-sequence-poset P u →
    is-constant-sequence u
  constant-is-increasing-decreasing-sequence-poset I J p q =
    rec-coproduct
      ( λ H → antisymmetric-leq-Poset P (u p) (u q) (I p q H) (J p q H))
      ( λ H → antisymmetric-leq-Poset P (u p) (u q) (J q p H) (I q p H))
      ( linear-leq-ℕ p q)
```
