# The negation isometry on real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.isometry-negation-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
```

</details>

## Idea

[Negation](real-numbers.negation-real-numbers.md) of real numbers is an
[isometry](metric-spaces.isometries-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definitions

### Negation of a real number preserves neighborhoods

```agda
module _
  {l1 : Level}
  where

  neg-neighborhood-leq-ℝ : (d : ℚ⁺) (x y : ℝ l1) →
    is-in-neighborhood-leq-ℝ l1 d x y →
    is-in-neighborhood-leq-ℝ l1 d (neg-ℝ x) (neg-ℝ y)
  neg-neighborhood-leq-ℝ d x y H =
    neighborhood-real-bound-each-leq-ℝ
      ( d)
      ( neg-ℝ x)
      ( neg-ℝ y)
      ( reverses-lower-neighborhood-leq-neg-ℝ
        ( d)
        ( y)
        ( x)
        ( right-real-bound-neighborhood-leq-ℝ d x y H))
      ( reverses-lower-neighborhood-leq-neg-ℝ
        ( d)
        ( x)
        ( y)
        ( left-real-bound-neighborhood-leq-ℝ d x y H))
```

### Negation on the real numbers is an isometry

```agda
module _
  {l1 : Level}
  where

  is-isometry-neg-ℝ :
    is-isometry-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-leq-ℝ l1)
      ( neg-ℝ)
  is-isometry-neg-ℝ d x y =
    ( neg-neighborhood-leq-ℝ d x y) ,
    ( ( binary-tr
        ( is-in-neighborhood-leq-ℝ l1 d)
        ( neg-neg-ℝ x)
        ( neg-neg-ℝ y)) ∘
      ( neg-neighborhood-leq-ℝ
        ( d)
        ( neg-ℝ x)
        ( neg-ℝ y)))

  isometry-neg-ℝ :
    isometry-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-leq-ℝ l1)
  isometry-neg-ℝ = (neg-ℝ , is-isometry-neg-ℝ)
```
