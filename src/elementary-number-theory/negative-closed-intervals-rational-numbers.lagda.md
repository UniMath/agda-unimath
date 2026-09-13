# Negative closed intervals in the rational numbers

```agda
module elementary-number-theory.negative-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.negative-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
of [rational numbers](elementary-number-theory.rational-numbers.md) is
{{#concept "negative" Disambiguation="closed intervals in ℚ" Agda=is-negative-closed-interval-ℚ}}
if every element in it is
[negative](elementary-number-theory.negative-rational-numbers.md), or
equivalently, its upper bound is negative.

## Definition

```agda
is-negative-prop-closed-interval-ℚ : closed-interval-ℚ → Prop lzero
is-negative-prop-closed-interval-ℚ ((a , b) , _) = is-negative-prop-ℚ b

is-negative-closed-interval-ℚ : closed-interval-ℚ → UU lzero
is-negative-closed-interval-ℚ ((a , b) , _) = is-negative-ℚ b

abstract
  is-negative-lower-bound-is-negative-closed-interval-ℚ :
    ([a,b] : closed-interval-ℚ) → is-negative-closed-interval-ℚ [a,b] →
    is-negative-ℚ (lower-bound-closed-interval-ℚ [a,b])
  is-negative-lower-bound-is-negative-closed-interval-ℚ ((a , b) , a≤b) neg-b =
    is-negative-leq-ℚ⁻ (b , neg-b) a≤b
```
