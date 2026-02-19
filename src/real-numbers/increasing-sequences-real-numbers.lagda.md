# Increasing sequences in the real numbers

```agda
module real-numbers.increasing-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences

open import order-theory.increasing-sequences-posets
open import order-theory.posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
```

</details>

## Idea

A [sequence](lists.sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) is
{{#concept "increasing" Disambiguation="sequence in ℝ" Agda=is-increasing-sequence-ℝ}}
if it is [increasing](order-theory.increasing-sequences-posets.md) in the
[poset of real numbers](real-numbers.inequality-real-numbers.md).

## Definition

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  is-increasing-prop-sequence-ℝ : Prop l
  is-increasing-prop-sequence-ℝ =
    is-increasing-prop-sequence-Poset (ℝ-Poset l) u

  is-increasing-sequence-ℝ : UU l
  is-increasing-sequence-ℝ = type-Prop is-increasing-prop-sequence-ℝ
```

## Properties

### `aₙ` is increasing if and only if for all n, `aₙ ≤ aₙ₊₁`

```agda
module _
  {l : Level}
  (u : sequence (ℝ l))
  where

  abstract
    is-increasing-leq-succ-sequence-ℝ :
      ((n : ℕ) → leq-ℝ (u n) (u (succ-ℕ n))) → is-increasing-sequence-ℝ u
    is-increasing-leq-succ-sequence-ℝ =
      is-increasing-leq-succ-sequence-Poset (ℝ-Poset l) u

    leq-succ-is-increasing-sequence-ℝ :
      is-increasing-sequence-ℝ u → (n : ℕ) → leq-ℝ (u n) (u (succ-ℕ n))
    leq-succ-is-increasing-sequence-ℝ =
      leq-succ-is-increasing-sequence-Poset (ℝ-Poset l) u
```
