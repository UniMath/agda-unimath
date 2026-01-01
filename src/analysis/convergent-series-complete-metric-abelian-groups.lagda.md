# Convergent series in complete metric abelian groups

```agda
module analysis.convergent-series-complete-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.complete-metric-abelian-groups
open import analysis.convergent-series-metric-abelian-groups
open import analysis.series-complete-metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
```

</details>

## Idea

A [series](analysis.series-metric-abelian-groups.md)
[converges](analysis.convergent-series-metric-abelian-groups.md) in a
[complete metric abelian group](analysis.complete-metric-abelian-groups.md) if
its partial sums form a
[Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md).

A slightly modified converse is also true: if a series converges, there
[exists](foundation.existential-quantification.md) a modulus making it a Cauchy
sequence.

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Complete-Metric-Ab l1 l2)
  (σ : series-Complete-Metric-Ab G)
  where

  is-sum-prop-series-Complete-Metric-Ab : type-Complete-Metric-Ab G → Prop l2
  is-sum-prop-series-Complete-Metric-Ab = is-sum-prop-series-Metric-Ab σ

  is-sum-series-Complete-Metric-Ab : type-Complete-Metric-Ab G → UU l2
  is-sum-series-Complete-Metric-Ab = is-sum-series-Metric-Ab σ

  is-convergent-prop-series-Complete-Metric-Ab : Prop (l1 ⊔ l2)
  is-convergent-prop-series-Complete-Metric-Ab =
    is-convergent-prop-series-Metric-Ab σ

  is-convergent-series-Complete-Metric-Ab : UU (l1 ⊔ l2)
  is-convergent-series-Complete-Metric-Ab = is-convergent-series-Metric-Ab σ

convergent-series-Complete-Metric-Ab :
  {l1 l2 : Level} (G : Complete-Metric-Ab l1 l2) → UU (l1 ⊔ l2)
convergent-series-Complete-Metric-Ab G =
  type-subtype (is-convergent-prop-series-Complete-Metric-Ab G)
```

## Properties

### If the partial sums of a series form a Cauchy sequence, the series converges

```agda
module _
  {l1 l2 : Level}
  (G : Complete-Metric-Ab l1 l2)
  (σ : series-Complete-Metric-Ab G)
  where

  is-convergent-series-is-cauchy-sequence-partial-sum-series-Complete-Metric-Ab :
    is-cauchy-sequence-Metric-Space
      ( metric-space-Complete-Metric-Ab G)
      ( partial-sum-series-Complete-Metric-Ab G σ) →
    is-convergent-series-Complete-Metric-Ab G σ
  is-convergent-cauchy-modulus-partial-sum-series-Complete-Metric-Ab H =
    has-limit-cauchy-sequence-Complete-Metric-Space
      ( complete-metric-space-Complete-Metric-Ab G)
      ( partial-sum-series-Complete-Metric-Ab G σ , H)
```

### If a series converges, its partial sums are a Cauchy sequence

```agda
module _
  {l1 l2 : Level}
  (G : Complete-Metric-Ab l1 l2)
  (σ : series-Complete-Metric-Ab G)
  where

  abstract
    is-cauchy-sequence-partial-sum-series-is-convergent-series-Complete-Metric-Ab :
      is-convergent-series-Complete-Metric-Ab G σ →
      is-cauchy-sequence-Metric-Space
        ( metric-space-Complete-Metric-Ab G)
        ( partial-sum-series-Complete-Metric-Ab G σ)
    is-cauchy-sequence-partial-sum-is-convergent-series-Complete-Metric-Ab =
      is-cauchy-has-limit-sequence-Metric-Space
        ( metric-space-Complete-Metric-Ab G)
```
