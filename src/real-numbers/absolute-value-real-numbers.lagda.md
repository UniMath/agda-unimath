# The absolute value of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.universe-levels
open import foundation.function-types
open import foundation.empty-types

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The absolute value of a [real number](real-numbers.dedekind-real-numbers.md) is
the [maximum](real-numbers.maximum-real-numbers.md) of it and its negation.

```agda
abs-ℝ : {l : Level} → ℝ l → ℝ l
abs-ℝ x = binary-max-ℝ x (neg-ℝ x)
```

## Properties

### The absolute value of a real number is nonnegative

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  is-nonnegative-abs-ℝ : is-nonnegative-ℝ (abs-ℝ x)
  is-nonnegative-abs-ℝ q q<0 =
    elim-disjunction
      ( lower-cut-ℝ (abs-ℝ x) q)
      ( id)
      ( λ (x<0 , 0<x) → ex-falso (is-disjoint-cut-ℝ x zero-ℚ (0<x , x<0)))
      ( is-located-lower-upper-cut-ℝ (abs-ℝ x) q zero-ℚ q<0)
```
