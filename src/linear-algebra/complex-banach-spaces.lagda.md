# Complex Banach spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.complex-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.metric-space-of-complex-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.complex-vector-spaces
open import linear-algebra.normed-complex-vector-spaces

open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A
{{#concept "complex Banach space" WDID=Q194397 WD="Banach space" Agda=ℂ-Banach-Space}}
is a [normed](linear-algebra.normed-complex-vector-spaces.md)
[complex vector space](linear-algebra.complex-vector-spaces.md) such that the
[metric space](metric-spaces.metric-spaces.md) induced by the norm is
[complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
is-banach-prop-Normed-ℂ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℂ-Vector-Space l1 l2) → Prop (l1 ⊔ l2)
is-banach-prop-Normed-ℂ-Vector-Space V =
  is-complete-prop-Metric-Space (metric-space-Normed-ℂ-Vector-Space V)

is-banach-Normed-ℂ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℂ-Vector-Space l1 l2) → UU (l1 ⊔ l2)
is-banach-Normed-ℂ-Vector-Space V =
  type-Prop (is-banach-prop-Normed-ℂ-Vector-Space V)

ℂ-Banach-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℂ-Banach-Space l1 l2 =
  type-subtype (is-banach-prop-Normed-ℂ-Vector-Space {l1} {l2})

module _
  {l1 l2 : Level}
  (V : ℂ-Banach-Space l1 l2)
  where

  normed-vector-space-ℂ-Banach-Space : Normed-ℂ-Vector-Space l1 l2
  normed-vector-space-ℂ-Banach-Space = pr1 V

  vector-space-ℂ-Banach-Space : ℂ-Vector-Space l1 l2
  vector-space-ℂ-Banach-Space =
    vector-space-Normed-ℂ-Vector-Space normed-vector-space-ℂ-Banach-Space

  ab-ℂ-Banach-Space : Ab l2
  ab-ℂ-Banach-Space = ab-ℂ-Vector-Space vector-space-ℂ-Banach-Space

  type-ℂ-Banach-Space : UU l2
  type-ℂ-Banach-Space = type-Ab ab-ℂ-Banach-Space

  add-ℂ-Banach-Space :
    type-ℂ-Banach-Space → type-ℂ-Banach-Space → type-ℂ-Banach-Space
  add-ℂ-Banach-Space = add-Ab ab-ℂ-Banach-Space

  neg-ℂ-Banach-Space : type-ℂ-Banach-Space → type-ℂ-Banach-Space
  neg-ℂ-Banach-Space = neg-Ab ab-ℂ-Banach-Space

  mul-ℂ-Banach-Space : ℂ l1 → type-ℂ-Banach-Space → type-ℂ-Banach-Space
  mul-ℂ-Banach-Space = mul-ℂ-Vector-Space vector-space-ℂ-Banach-Space

  zero-ℂ-Banach-Space : type-ℂ-Banach-Space
  zero-ℂ-Banach-Space = zero-Ab ab-ℂ-Banach-Space

  metric-space-ℂ-Banach-Space : Metric-Space l2 l1
  metric-space-ℂ-Banach-Space =
    metric-space-Normed-ℂ-Vector-Space normed-vector-space-ℂ-Banach-Space

  is-complete-metric-space-ℂ-Banach-Space :
    is-complete-Metric-Space metric-space-ℂ-Banach-Space
  is-complete-metric-space-ℂ-Banach-Space = pr2 V
```

## Properties

### The complex numbers are a complex Banach space over themselves

```agda
abstract
  is-banach-normed-complex-vector-space-ℂ :
    (l : Level) →
    is-banach-Normed-ℂ-Vector-Space (normed-complex-vector-space-ℂ l)
  is-banach-normed-complex-vector-space-ℂ l =
    tr
      ( is-complete-Metric-Space)
      ( eq-metric-space-ℂ-metric-space-normed-complex-vector-space-ℂ l)
      ( is-complete-metric-space-ℂ l)

complex-banach-space-ℂ : (l : Level) → ℂ-Banach-Space l (lsuc l)
complex-banach-space-ℂ l =
  ( normed-complex-vector-space-ℂ l ,
    is-banach-normed-complex-vector-space-ℂ l)
```
