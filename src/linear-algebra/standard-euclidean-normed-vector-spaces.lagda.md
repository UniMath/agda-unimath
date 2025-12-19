# The standard Euclidean normed vector spaces

```agda
module linear-algebra.standard-euclidean-normed-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.function-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-inner-product-spaces-are-normed
open import linear-algebra.standard-euclidean-inner-product-spaces

open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.lipschitz-functions-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The standard Euclidean
[normed vector space](linear-algebra.normed-real-vector-spaces.md) `ℝⁿ` has the
norm $v ↦ \sqrt{\sum vᵢ^2}$.

## Definition

```agda
normed-vector-space-ℝ^ : ℕ → (l : Level) → Normed-ℝ-Vector-Space l (lsuc l)
normed-vector-space-ℝ^ n l =
  normed-vector-space-ℝ-Inner-Product-Space (inner-product-space-ℝ^ n l)

euclidean-metric-space-ℝ^ : ℕ → (l : Level) → Metric-Space (lsuc l) l
euclidean-metric-space-ℝ^ n l =
  metric-space-Normed-ℝ-Vector-Space (normed-vector-space-ℝ^ n l)
```
