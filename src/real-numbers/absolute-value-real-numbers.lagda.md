# The absolute value of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.absolute-value-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.negation-real-numbers
```

</details>

## Idea

The absolute value of a [real number](real-numbers.dedekind-real-numbers.md)
is the [maximum](real-numbers.maximum-real-numbers.md) of it and its negation.

```agda
abs-ℝ : {l : Level} → ℝ l → ℝ l
abs-ℝ x = binary-max-ℝ x (neg-ℝ x)
```

## Properties

### The absolute value of a real number is nonnegative

```agda

```
