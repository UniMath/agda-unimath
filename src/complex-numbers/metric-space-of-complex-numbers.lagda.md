# The metric space of complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.metric-space-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.difference-complex-numbers
open import complex-numbers.distance-complex-numbers
open import complex-numbers.equivalence-complex-numbers-two-dimensional-vector-space-real-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import functional-analysis.standard-euclidean-hilbert-spaces

open import linear-algebra.standard-euclidean-inner-product-spaces

open import metric-spaces.complete-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.rational-neighborhood-relations

open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The standard [metric space](metric-spaces.metric-spaces.md) of
[complex numbers](complex-numbers.complex-numbers.md) is isomorphic to the
[standard Euclidean metric space](linear-algebra.standard-euclidean-inner-product-spaces.md)
`ℝ²`.

## Definition

```agda
abstract
  is-metric-dist-ℂ :
    (l : Level) →
    is-metric-distance-function
      ( ℂ-Set l)
      ( nonnegative-dist-ℂ)
  is-metric-dist-ℂ l =
    ( refl-dist-ℂ ,
      ( λ z w → eq-ℝ⁰⁺ _ _ (symmetric-dist-ℂ z w)) ,
      triangular-dist-ℂ ,
      ( λ z w |z-w|=0 → eq-sim-ℂ (is-extensional-dist-ℂ z w |z-w|=0)))

metric-ℂ : (l : Level) → Metric l (ℂ-Set l)
metric-ℂ l = ( nonnegative-dist-ℂ , is-metric-dist-ℂ l)

metric-space-ℂ : (l : Level) → Metric-Space (lsuc l) l
metric-space-ℂ l = metric-space-Metric (ℂ-Set l) (metric-ℂ l)

neighborhood-prop-ℂ : (l : Level) → Rational-Neighborhood-Relation l (ℂ l)
neighborhood-prop-ℂ l = neighborhood-prop-Metric-Space (metric-space-ℂ l)

neighborhood-ℂ : (l : Level) → ℚ⁺ → Relation l (ℂ l)
neighborhood-ℂ l = neighborhood-Metric-Space (metric-space-ℂ l)
```

## Properties

### The isometric equivalence between the metric space on `ℂ` and the Euclidean metric space `ℝ²`

```agda
isometric-equiv-metric-space-ℂ-euclidean-metric-space-ℝ² :
  (l : Level) →
  isometric-equiv-Metric-Space
    ( metric-space-ℂ l)
    ( euclidean-metric-space-ℝ-Fin 2 l)
isometric-equiv-metric-space-ℂ-euclidean-metric-space-ℝ² l =
  ( equiv-ℂ-ℝ² l ,
    λ d z w →
      iff-equiv
        ( equiv-tr
          ( λ x → leq-ℝ x (real-ℚ⁺ d))
          ( ( magnitude-complex-ℝ² (z -ℂ w)) ∙
            ( ap euclidean-norm-ℝ-Fin (diff-complex-ℝ² z w)))))

abstract
  eq-metric-space-ℂ-metric-space-ℝ² :
    (l : Level) →
    metric-space-ℂ l ＝ euclidean-metric-space-ℝ-Fin 2 l
  eq-metric-space-ℂ-metric-space-ℝ² l =
    eq-isometric-equiv-Metric-Space
      ( metric-space-ℂ l)
      ( euclidean-metric-space-ℝ-Fin 2 l)
      ( isometric-equiv-metric-space-ℂ-euclidean-metric-space-ℝ² l)
```

### The metric space on `ℂ` is complete

```agda
abstract
  is-complete-metric-space-ℂ :
    (l : Level) → is-complete-Metric-Space (metric-space-ℂ l)
  is-complete-metric-space-ℂ l =
    inv-tr
      ( is-complete-Metric-Space)
      ( eq-metric-space-ℂ-metric-space-ℝ² l)
      ( is-complete-euclidean-metric-space-ℝ-Fin 2 l)

complete-metric-space-ℂ : (l : Level) → Complete-Metric-Space (lsuc l) l
complete-metric-space-ℂ l =
  ( metric-space-ℂ l , is-complete-metric-space-ℂ l)
```
