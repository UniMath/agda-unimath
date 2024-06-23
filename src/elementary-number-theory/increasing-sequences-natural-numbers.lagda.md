# Increasing sequences of natural numbers

```agda
module elementary-number-theory.increasing-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strictly-increasing-sequences-natural-numbers

open import foundation.constant-sequences
open import foundation.coproduct-types
open import foundation.negation
open import foundation.propositions
open import foundation.sequences
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import order-theory.increasing-sequences-posets
open import order-theory.sequences-posets
```

</details>

## Idea

A sequence of natural numbers is **increasing** if it preserves
[inequality of natural numbers](elementary-number-theory.inequality-natural-numbers.md).

## Definitions

### Increasing values of sequences of natural numbers

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  is-increasing-value-sequence-ℕ : UU lzero
  is-increasing-value-sequence-ℕ =
    is-increasing-value-sequence-poset ℕ-Poset f n
```

### Increasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-sequence-ℕ : UU lzero
  is-increasing-sequence-ℕ = is-increasing-sequence-poset ℕ-Poset f
```

## Properties

### An increasing value of a sequence of natural numbers is either stationnary or strictly increasing

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  decide-is-stationnary-is-increasing-value-sequence-ℕ :
    is-increasing-value-sequence-ℕ f n →
    (is-stationnary-value-sequence f n) +
    (is-strict-increasing-value-sequence-ℕ f n)
  decide-is-stationnary-is-increasing-value-sequence-ℕ =
    eq-or-le-leq-ℕ (f n) (f (succ-ℕ n))
```

### Any value of an increasing sequence of natural numbers that is not a strict value is stationnary

```agda
module _
  (f : sequence ℕ)
  where

  stationnary-value-is-not-strict-value-increasing-sequence-ℕ :
    is-increasing-sequence-ℕ f →
    (n : ℕ) →
    ¬ (is-strict-increasing-value-sequence-ℕ f n) →
    is-stationnary-value-sequence f n
  stationnary-value-is-not-strict-value-increasing-sequence-ℕ H n K =
    map-right-unit-law-coproduct-is-empty
      ( is-stationnary-value-sequence f n)
      ( is-strict-increasing-value-sequence-ℕ f n)
      ( K)
      ( decide-is-stationnary-is-increasing-value-sequence-ℕ
        ( f)
        ( n)
        ( increasing-value-is-increasing-sequence-poset ℕ-Poset {f} H n))
```
