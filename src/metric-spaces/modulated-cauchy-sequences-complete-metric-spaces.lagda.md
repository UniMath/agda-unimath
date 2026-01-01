# Modulated Cauchy sequences in complete metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.modulated-cauchy-sequences-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.limits-of-modulated-cauchy-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
```

</details>

## Idea

A
[modulated Cauchy sequence](metric-spaces.modulated-cauchy-sequences-metric-spaces.md)
in a [complete metric space](metric-spaces.complete-metric-spaces.md) is a
Cauchy sequence in the underlying
[metric space](metric-spaces.metric-spaces.md). Modulated Cauchy sequences in
complete metric spaces always have a
[limit](metric-spaces.limits-of-modulated-cauchy-sequences-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level} (M : Complete-Metric-Space l1 l2)
  where

  modulated-cauchy-sequence-Complete-Metric-Space : UU (l1 ⊔ l2)
  modulated-cauchy-sequence-Complete-Metric-Space =
    modulated-cauchy-sequence-Metric-Space
      ( metric-space-Complete-Metric-Space M)

  is-limit-modulated-cauchy-sequence-Complete-Metric-Space :
    modulated-cauchy-sequence-Complete-Metric-Space →
    type-Complete-Metric-Space M →
    UU l2
  is-limit-modulated-cauchy-sequence-Complete-Metric-Space x l =
    is-limit-modulated-cauchy-sequence-Metric-Space
      ( metric-space-Complete-Metric-Space M)
      ( x)
      ( l)
```

## Properties

### Every Cauchy sequence in a complete metric space has a limit

```agda
module _
  {l1 l2 : Level}
  (M : Complete-Metric-Space l1 l2)
  (x : modulated-cauchy-sequence-Complete-Metric-Space M)
  where

  abstract
    has-limit-modulated-cauchy-sequence-Complete-Metric-Space :
      has-limit-modulated-cauchy-sequence-Metric-Space
        ( metric-space-Complete-Metric-Space M)
        ( x)
    has-limit-modulated-cauchy-sequence-Complete-Metric-Space =
      ind-Σ
        ( has-limit-modulated-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space
          ( metric-space-Complete-Metric-Space M)
          ( x))
        ( is-complete-metric-space-Complete-Metric-Space
          ( M)
          ( cauchy-approximation-modulated-cauchy-sequence-Metric-Space
            ( metric-space-Complete-Metric-Space M)
            ( x)))

    lim-modulated-cauchy-sequence-Complete-Metric-Space :
      type-Complete-Metric-Space M
    lim-modulated-cauchy-sequence-Complete-Metric-Space =
      pr1 has-limit-modulated-cauchy-sequence-Complete-Metric-Space

    is-limit-lim-modulated-cauchy-sequence-Complete-Metric-Space :
      is-limit-modulated-cauchy-sequence-Metric-Space
        ( metric-space-Complete-Metric-Space M)
        ( x)
        ( lim-modulated-cauchy-sequence-Complete-Metric-Space)
    is-limit-lim-modulated-cauchy-sequence-Complete-Metric-Space =
      pr2 has-limit-modulated-cauchy-sequence-Complete-Metric-Space
```

### If every modulated Cauchy sequence has a limit in a metric space, the metric space is complete

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  modulated-cauchy-sequences-have-limits-Metric-Space : UU (l1 ⊔ l2)
  modulated-cauchy-sequences-have-limits-Metric-Space =
    (x : modulated-cauchy-sequence-Metric-Space M) →
    has-limit-modulated-cauchy-sequence-Metric-Space M x

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (H : modulated-cauchy-sequences-have-limits-Metric-Space M)
  where

  is-complete-metric-space-modulated-cauchy-sequences-have-limits-Metric-Space :
    is-complete-Metric-Space M
  is-complete-metric-space-modulated-cauchy-sequences-have-limits-Metric-Space
    x =
    tot
      ( is-limit-cauchy-approximation-limit-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
        ( M)
        ( x))
      ( H (modulated-cauchy-sequence-cauchy-approximation-Metric-Space M x))

  complete-metric-space-modulated-cauchy-sequences-have-limits-Metric-Space :
    Complete-Metric-Space l1 l2
  complete-metric-space-modulated-cauchy-sequences-have-limits-Metric-Space =
    ( M ,
      is-complete-metric-space-modulated-cauchy-sequences-have-limits-Metric-Space)
```
