# Positive closed intervals in the rational numbers

```agda
module elementary-number-theory.positive-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
of [rational numbers](elementary-number-theory.rational-numbers.md) is
{{#concept "positive" Disambiguation="closed intervals in ℚ" Agda=is-positive-closed-interval-ℚ}}
if every element in it is
[positive](elementary-number-theory.positive-rational-numbers.md), or
equivalently, its lower bound is positive.

## Definition

```agda
is-positive-prop-closed-interval-ℚ : closed-interval-ℚ → Prop lzero
is-positive-prop-closed-interval-ℚ ((a , b) , _) = is-positive-prop-ℚ a

is-positive-closed-interval-ℚ : closed-interval-ℚ → UU lzero
is-positive-closed-interval-ℚ ((a , b) , _) = is-positive-ℚ a

abstract
  is-positive-upper-bound-is-positive-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) → is-positive-closed-interval-ℚ [a,b] →
    is-positive-ℚ (upper-bound-closed-interval-ℚ [a,b])
  is-positive-upper-bound-is-positive-closed-interval-ℚ ((a , b) , a≤b) pos-a =
    is-positive-leq-ℚ⁺ (a , pos-a) a≤b
```
