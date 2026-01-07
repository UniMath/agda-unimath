# The standard Euclidean Hilbert spaces

```agda
module functional-analysis.standard-euclidean-hilbert-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import functional-analysis.real-banach-spaces
open import functional-analysis.real-hilbert-spaces

open import linear-algebra.standard-euclidean-inner-product-spaces

open import metric-spaces.complete-metric-spaces
open import metric-spaces.uniform-homeomorphisms-metric-spaces

open import real-numbers.metric-space-of-functions-into-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
[standard Euclidean inner product space](linear-algebra.standard-euclidean-inner-product-spaces.md)
`ℝⁿ` is a [Hilbert space](functional-analysis.real-hilbert-spaces.md) (and
therefore a [Banach space](functional-analysis.real-banach-spaces.md)).

## Definition

```agda
abstract
  is-complete-euclidean-metric-space-ℝ^ :
    (n : ℕ) (l : Level) →
    is-complete-Metric-Space (euclidean-metric-space-ℝ^ n l)
  is-complete-euclidean-metric-space-ℝ^ n l =
    preserves-is-complete-uniform-homeomorphism-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-ℝ^ n l)
      ( uniform-homeomorphism-id-product-euclidean-metric-space-ℝ^ n l)
      ( is-complete-function-into-ℝ-Metric-Space (Fin n) l)

hilbert-space-ℝ^ : (n : ℕ) (l : Level) → ℝ-Hilbert-Space l (lsuc l)
hilbert-space-ℝ^ n l =
  ( inner-product-space-ℝ^ n l , is-complete-euclidean-metric-space-ℝ^ n l)

banach-space-ℝ^ : (n : ℕ) (l : Level) → ℝ-Banach-Space l (lsuc l)
banach-space-ℝ^ n l = banach-space-ℝ-Hilbert-Space (hilbert-space-ℝ^ n l)
```
