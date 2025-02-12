# The minimum of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.intersections-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

The minimum of two
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers) `x`, `y`
is a lower Dedekind real number with cut equal to the intersection of the cuts
of `x` and `y`.

The minimum of a family of lower Dedekind real numbers is not always a lower
Dedekind real number.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  binary-min-cut-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  binary-min-cut-lower-ℝ = intersection-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)

  is-inhabited-binary-min-cut-lower-ℝ : exists ℚ binary-min-cut-lower-ℝ
  is-inhabited-binary-min-cut-lower-ℝ =
    map-binary-exists
      ( is-in-subtype binary-min-cut-lower-ℝ)
      {!   !}
      {!   !}
      (is-inhabited-cut-lower-ℝ x)
      (is-inhabited-cut-lower-ℝ y)
```
