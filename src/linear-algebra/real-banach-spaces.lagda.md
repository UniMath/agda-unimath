# Real Banach spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import lists.sequences

open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

A real
{{#concept "Banach space" WDID=Q194397 WD="Banach space" Disambiguation="over the real numbers" Agda=ℝ-Banach-Space}}
is a [normed](linear-algebra.normed-real-vector-spaces.md)
[real vector space](linear-algebra.real-vector-spaces.md) such that the
[metric space](metric-spaces.metric-spaces.md) induced by the norm is
[complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
is-banach-prop-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) → Prop (l1 ⊔ l2)
is-banach-prop-Normed-ℝ-Vector-Space V =
  is-complete-prop-Metric-Space (metric-space-Normed-ℝ-Metric-Space V)

is-banach-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) → UU (l1 ⊔ l2)
is-banach-Normed-ℝ-Vector-Space V =
  type-Prop (is-banach-prop-Normed-ℝ-Vector-Space V)

ℝ-Banach-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Banach-Space l1 l2 =
  type-subtype (is-banach-prop-Normed-ℝ-Vector-Space {l1} {l2})

module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  where

  normed-vector-space-ℝ-Banach-Space : Normed-ℝ-Vector-Space l1 l2
  normed-vector-space-ℝ-Banach-Space = pr1 V

  metric-space-ℝ-Banach-Space : Metric-Space l2 l1
  metric-space-ℝ-Banach-Space =
    metric-space-Normed-ℝ-Metric-Space normed-vector-space-ℝ-Banach-Space

  is-complete-metric-space-ℝ-Banach-Space :
    is-complete-Metric-Space metric-space-ℝ-Banach-Space
  is-complete-metric-space-ℝ-Banach-Space = pr2 V

  complete-metric-space-ℝ-Banach-Space : Complete-Metric-Space l2 l1
  complete-metric-space-ℝ-Banach-Space =
    ( metric-space-ℝ-Banach-Space , is-complete-metric-space-ℝ-Banach-Space)

  type-ℝ-Banach-Space : UU l2
  type-ℝ-Banach-Space =
    type-Normed-ℝ-Vector-Space normed-vector-space-ℝ-Banach-Space

  map-norm-ℝ-Banach-Space : type-ℝ-Banach-Space → ℝ l1
  map-norm-ℝ-Banach-Space =
    map-norm-Normed-ℝ-Vector-Space normed-vector-space-ℝ-Banach-Space

  cauchy-sequence-ℝ-Banach-Space : UU (l1 ⊔ l2)
  cauchy-sequence-ℝ-Banach-Space =
    cauchy-sequence-Metric-Space metric-space-ℝ-Banach-Space

  is-cauchy-sequence-ℝ-Banach-Space :
    sequence type-ℝ-Banach-Space → UU l1
  is-cauchy-sequence-ℝ-Banach-Space =
    is-cauchy-sequence-Metric-Space metric-space-ℝ-Banach-Space

  map-cauchy-sequence-ℝ-Banach-Space :
    cauchy-sequence-ℝ-Banach-Space → sequence type-ℝ-Banach-Space
  map-cauchy-sequence-ℝ-Banach-Space = pr1

  has-limit-sequence-ℝ-Banach-Space :
    sequence type-ℝ-Banach-Space → UU (l1 ⊔ l2)
  has-limit-sequence-ℝ-Banach-Space =
    has-limit-sequence-Metric-Space metric-space-ℝ-Banach-Space

  has-limit-cauchy-sequence-ℝ-Banach-Space :
    (σ : cauchy-sequence-ℝ-Banach-Space) →
    has-limit-sequence-ℝ-Banach-Space (map-cauchy-sequence-ℝ-Banach-Space σ)
  has-limit-cauchy-sequence-ℝ-Banach-Space =
    has-limit-cauchy-sequence-Complete-Metric-Space
      ( complete-metric-space-ℝ-Banach-Space)

  dist-ℝ-Banach-Space : (u v : type-ℝ-Banach-Space) → ℝ l1
  dist-ℝ-Banach-Space =
    dist-Normed-ℝ-Vector-Space normed-vector-space-ℝ-Banach-Space

  commutative-dist-ℝ-Banach-Space :
    (u v : type-ℝ-Banach-Space) →
    dist-ℝ-Banach-Space u v ＝ dist-ℝ-Banach-Space v u
  commutative-dist-ℝ-Banach-Space =
    commutative-dist-Normed-ℝ-Vector-Space normed-vector-space-ℝ-Banach-Space

  diff-ℝ-Banach-Space :
    type-ℝ-Banach-Space → type-ℝ-Banach-Space → type-ℝ-Banach-Space
  diff-ℝ-Banach-Space =
    diff-Normed-ℝ-Vector-Space normed-vector-space-ℝ-Banach-Space
```
