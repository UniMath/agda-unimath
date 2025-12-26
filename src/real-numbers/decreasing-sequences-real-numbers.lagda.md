# Decreasing sequences in the real numbers

```agda
module real-numbers.decreasing-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import order-theory.decreasing-sequences-posets
open import order-theory.posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
```

</details>

## Idea

A [sequence](lists.sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) is
{{#concept "decreasing" Disambiguation="sequence in ℝ" Agda=is-decreasing-sequence-ℝ}}
if it is [decreasing](order-theory.decreasing-sequences-posets.md) in the
[poset of real numbers](real-numbers.inequality-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  is-decreasing-prop-sequence-ℝ : Prop l
  is-decreasing-prop-sequence-ℝ =
    is-decreasing-prop-sequence-Poset (ℝ-Poset l) u

  is-decreasing-sequence-ℝ : UU l
  is-decreasing-sequence-ℝ = type-Prop is-decreasing-prop-sequence-ℝ
```

## Properties

### `aₙ` is decreasing if and only if for all n, `aₙ ≤ aₙ₊₁`

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  abstract
    is-decreasing-leq-succ-sequence-ℝ :
      ((n : ℕ) → leq-ℝ (u (succ-ℕ n)) (u n)) → is-decreasing-sequence-ℝ u
    is-decreasing-leq-succ-sequence-ℝ =
      is-decreasing-leq-succ-sequence-Poset (ℝ-Poset l) u

    leq-succ-is-decreasing-sequence-ℝ :
      is-decreasing-sequence-ℝ u → (n : ℕ) → leq-ℝ (u (succ-ℕ n)) (u n)
    leq-succ-is-decreasing-sequence-ℝ =
      leq-succ-is-decreasing-sequence-Poset (ℝ-Poset l) u
```
