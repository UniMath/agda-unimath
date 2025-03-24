# The absolute value function on the rational numbers

```agda
module elementary-number-theory.absolute-value-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
```

</details>

## Idea

The {{#concept "absolute value" Disambiguation="of a rational number" Agda=abs-ℚ WD="absolute value" WDID=Q120812}}
a rational number is the greater of itself and its negation.

## Definition

```agda
rational-abs-ℚ : ℚ → ℚ
rational-abs-ℚ q = max-ℚ q (neg-ℚ q)

is-nonnegative-rational-abs-ℚ : (q : ℚ) → is-nonnegative-ℚ (rational-abs-ℚ q)

abs-ℚ : ℚ → ℚ⁰⁺
pr1 (abs-ℚ q) = rational-abs-ℚ q
```

## Properties
