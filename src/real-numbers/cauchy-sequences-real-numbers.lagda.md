# Cauchy sequences in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.cauchy-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.cauchy-sequences-complete-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.images-cauchy-sequences-uniformly-continuous-maps-metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "Cauchy sequence" Disambiguation="in the Dedekind real numbers" Agda=cauchy-sequence-ℝ}}
is a [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) in the
[metric space](metric-spaces.metric-spaces.md) of
[real numbers](real-numbers.dedekind-real-numbers.md). Because the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md)
[is complete](real-numbers.cauchy-completeness-dedekind-real-numbers.md), a
[sequence](lists.sequences.md) of real numbers has a
[convergence modulus](metric-spaces.convergent-sequences-metric-spaces.md)
[if and only if](foundation.logical-equivalences.md) it is Cauchy.

## Definition

```agda
is-cauchy-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU l
is-cauchy-sequence-ℝ {l} = is-cauchy-sequence-Metric-Space (metric-space-ℝ l)

cauchy-sequence-ℝ : (l : Level) → UU (lsuc l)
cauchy-sequence-ℝ l = cauchy-sequence-Metric-Space (metric-space-ℝ l)
```

## Properties

### All Cauchy sequences in ℝ have a limit

```agda
lim-cauchy-sequence-ℝ : {l : Level} → cauchy-sequence-ℝ l → ℝ l
lim-cauchy-sequence-ℝ {l} =
  lim-cauchy-sequence-Complete-Metric-Space (complete-metric-space-ℝ l)
```

### The sum of Cauchy sequences is a Cauchy sequence

```agda
add-cauchy-sequence-ℝ :
  {l1 l2 : Level} → cauchy-sequence-ℝ l1 → cauchy-sequence-ℝ l2 →
  cauchy-sequence-ℝ (l1 ⊔ l2)
add-cauchy-sequence-ℝ {l1} {l2} u v =
  map-uniformly-continuous-map-cauchy-sequence-Metric-Space
    ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
    ( metric-space-ℝ (l1 ⊔ l2))
    ( uniformly-continuous-add-pair-ℝ l1 l2)
    ( pair-cauchy-sequence-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-ℝ l2)
      ( u)
      ( v))
```

### If a sequence has a limit, it is Cauchy

```agda
abstract
  is-cauchy-has-limit-sequence-ℝ :
    {l : Level} (σ : sequence (ℝ l)) →
    has-limit-sequence-ℝ σ → is-cauchy-sequence-ℝ σ
  is-cauchy-has-limit-sequence-ℝ {l} σ =
    is-cauchy-has-limit-sequence-Metric-Space (metric-space-ℝ l)
```
