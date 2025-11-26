# Real Banach spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.complete-metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
```

</details>

## Idea

A
{{#concept "real Banach space" WDID=Q194397 WD="Banach space" Agda=ℝ-Banach-Space}}
is a [normed](linear-algebra.normed-real-vector-spaces.md)
[real vector space](linear-algebra.real-vector-spaces.md) such that the
[metric space](metric-spaces.metric-spaces.md) induced by the norm is
[complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
is-banach-prop-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) → Prop (l1 ⊔ l2)
is-banach-prop-Normed-ℝ-Vector-Space V =
  is-complete-prop-Metric-Space (metric-space-Normed-ℝ-Vector-Space V)

is-banach-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) → UU (l1 ⊔ l2)
is-banach-Normed-ℝ-Vector-Space V =
  type-Prop (is-banach-prop-Normed-ℝ-Vector-Space V)

ℝ-Banach-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Banach-Space l1 l2 =
  type-subtype (is-banach-prop-Normed-ℝ-Vector-Space {l1} {l2})
```

## Properties

### The real numbers are a real Banach space with norm `x ↦ |x|`

```agda
abstract
  is-banach-normed-real-vector-space-ℝ :
    (l : Level) →
    is-banach-Normed-ℝ-Vector-Space (normed-real-vector-space-ℝ l)
  is-banach-normed-real-vector-space-ℝ l =
    inv-tr
      ( is-complete-Metric-Space)
      ( eq-metric-space-normed-real-vector-space-metric-space-ℝ l)
      ( is-complete-metric-space-ℝ l)

real-banach-space-ℝ : (l : Level) → ℝ-Banach-Space l (lsuc l)
real-banach-space-ℝ l =
  ( normed-real-vector-space-ℝ l ,
    is-banach-normed-real-vector-space-ℝ l)
```

## External links

- [Banach space](https://en.wikipedia.org/wiki/Banach_space) on Wikipedia
