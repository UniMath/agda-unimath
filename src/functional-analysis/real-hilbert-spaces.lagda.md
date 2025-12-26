# Real Hilbert spaces

```agda
{-# OPTIONS --lossy-unification #-}

module functional-analysis.real-hilbert-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import functional-analysis.normed-real-vector-spaces
open import functional-analysis.real-banach-spaces

open import linear-algebra.real-inner-product-spaces
open import linear-algebra.real-inner-product-spaces-are-normed

open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
```

</details>

## Idea

A
{{#concept "real Hilbert space" WDID=Q190056 WD="Hilbert space" Agda=ℝ-Hilbert-Space}}
is a [real inner product space](linear-algebra.real-inner-product-spaces.md) for
which the [metric space](metric-spaces.metric-spaces.md)
[induced](linear-algebra.real-inner-product-spaces-are-normed.md) by the inner
product is [complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  is-complete-prop-ℝ-Inner-Product-Space : Prop (l1 ⊔ l2)
  is-complete-prop-ℝ-Inner-Product-Space =
    is-complete-prop-Metric-Space
      ( metric-space-ℝ-Inner-Product-Space V)

  is-complete-ℝ-Inner-Product-Space : UU (l1 ⊔ l2)
  is-complete-ℝ-Inner-Product-Space =
    type-Prop is-complete-prop-ℝ-Inner-Product-Space

ℝ-Hilbert-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Hilbert-Space l1 l2 =
  type-subtype (is-complete-prop-ℝ-Inner-Product-Space {l1} {l2})
```

## Properties

### Every real Hilbert space is a real Banach space

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Hilbert-Space l1 l2)
  where

  inner-product-space-ℝ-Hilbert-Space : ℝ-Inner-Product-Space l1 l2
  inner-product-space-ℝ-Hilbert-Space = pr1 V

  normed-vector-space-ℝ-Hilbert-Space : Normed-ℝ-Vector-Space l1 l2
  normed-vector-space-ℝ-Hilbert-Space =
    normed-vector-space-ℝ-Inner-Product-Space
      ( inner-product-space-ℝ-Hilbert-Space)

  banach-space-ℝ-Hilbert-Space : ℝ-Banach-Space l1 l2
  banach-space-ℝ-Hilbert-Space =
    ( normed-vector-space-ℝ-Hilbert-Space , pr2 V)
```

### The real numbers are a real Hilbert space with multiplication as the inner product

```agda
abstract
  is-complete-real-inner-product-space-ℝ :
    (l : Level) →
    is-complete-ℝ-Inner-Product-Space (real-inner-product-space-ℝ l)
  is-complete-real-inner-product-space-ℝ l =
    inv-tr
      ( is-complete-Metric-Space)
      ( eq-metric-space-real-inner-product-space-ℝ l)
      ( is-complete-metric-space-ℝ l)

real-hilbert-space-ℝ : (l : Level) → ℝ-Hilbert-Space l (lsuc l)
real-hilbert-space-ℝ l =
  ( real-inner-product-space-ℝ l ,
    is-complete-real-inner-product-space-ℝ l)
```

## See also

- [Real Banach spaces](functional-analysis.real-banach-spaces.md)

## External links

- [Hilbert space](https://en.wikipedia.org/wiki/Hilbert_space) on Wikipedia
- [Hilbert space](https://ncatlab.org/nlab/show/Hilbert+space) on $n$Lab
