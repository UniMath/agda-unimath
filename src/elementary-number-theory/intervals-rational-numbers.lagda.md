# Intervals in the rational numbers

```agda
module elementary-number-theory.intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.closed-intervals-posets
```

</details>

## Idea

An interval in the rational numbers is a
[closed interval](order-theory.closed-intervals-posets.md) in the
[poset](elementary-number-theory.inequality-rational-numbers.md) of
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
interval-ℚ : UU lzero
interval-ℚ = closed-interval-Poset ℚ-Poset

lower-bound-interval-ℚ : interval-ℚ → ℚ
lower-bound-interval-ℚ =
  lower-bound-closed-interval-Poset ℚ-Poset

upper-bound-interval-ℚ : interval-ℚ → ℚ
upper-bound-interval-ℚ =
  lower-bound-closed-interval-Poset ℚ-Poset

subtype-interval-ℚ : interval-ℚ → subtype lzero ℚ
subtype-interval-ℚ = subposet-closed-interval-Poset ℚ-Poset

is-closed-interval-map-prop-ℚ :
  (ℚ → ℚ) → interval-ℚ → interval-ℚ → Prop ?
```
