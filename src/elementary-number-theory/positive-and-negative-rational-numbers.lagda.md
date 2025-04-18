# The positive, negative, and nonnegative rational numbers

```agda
module elementary-number-theory.positive-and-negative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
```

</details>

## Idea

In this file, we outline basic relations between
[negative](elementary-number-theory.negative-rational-numbers.md),
[nonnegative](elementary-number-theory.nonnegative-rational-numbers.md), and
[positive](elementary-number-theory.positive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md).

## Properties

### Dichotomies

#### A rational number is either negative or nonnegative

```agda
abstract
  decide-is-negative-is-nonnegative-ℚ :
    (q : ℚ) →
    is-negative-ℚ q + is-nonnegative-ℚ q
  decide-is-negative-is-nonnegative-ℚ q =
    map-coproduct
      ( is-negative-le-zero-ℚ q)
      ( is-nonnegative-leq-zero-ℚ q)
      ( decide-le-leq-ℚ q zero-ℚ)
```
