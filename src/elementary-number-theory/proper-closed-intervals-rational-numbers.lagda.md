# Proper closed intervals in the rational numbers

```agda
module elementary-number-theory.proper-closed-intervals-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
of [rational numbers](elementary-number-theory.rational-numbers.md) is said to
be {{#concept "proper" Disambiguation="closed interval of rational numbers" Agda=is-proper-closed-interval-ℚ}} if its lower bound is
[strictly less than](elementary-number-theory.strict-inequality-rational-numbers.md)
its upper bound, or equivalently, it contains more than one element.

## Definition

```agda
is-proper-prop-closed-interval-ℚ : closed-interval-ℚ → Prop lzero
is-proper-prop-closed-interval-ℚ ((a , b) , _) = le-ℚ-Prop a b

is-proper-closed-interval-ℚ : closed-interval-ℚ → UU lzero
is-proper-closed-interval-ℚ [a,b] =
  type-Prop (is-proper-prop-closed-interval-ℚ [a,b])
```
