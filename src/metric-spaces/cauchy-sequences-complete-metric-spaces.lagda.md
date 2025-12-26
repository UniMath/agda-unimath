# Cauchy sequences in complete metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-sequences-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-complete-metric-spaces
```

</details>

## Idea

A [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) in a
[complete metric space](metric-spaces.complete-metric-spaces.md) is a Cauchy
sequence in the underlying [metric space](metric-spaces.metric-spaces.md).
Cauchy sequences in complete metric spaces always have a limit.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Complete-Metric-Space l1 l2)
  where

  cauchy-sequence-Complete-Metric-Space : UU (l1 ⊔ l2)
  cauchy-sequence-Complete-Metric-Space =
    cauchy-sequence-Metric-Space (metric-space-Complete-Metric-Space M)

  is-limit-cauchy-sequence-Complete-Metric-Space :
    cauchy-sequence-Complete-Metric-Space → type-Complete-Metric-Space M → UU l2
  is-limit-cauchy-sequence-Complete-Metric-Space x l =
    is-limit-cauchy-sequence-Metric-Space
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
  where

  abstract
    has-limit-cauchy-sequence-Complete-Metric-Space :
      (x : cauchy-sequence-Complete-Metric-Space M) →
      has-limit-cauchy-sequence-Metric-Space
        ( metric-space-Complete-Metric-Space M)
        ( x)
    has-limit-cauchy-sequence-Complete-Metric-Space cx@(x , is-cauchy-x) =
      rec-trunc-Prop
        ( has-limit-prop-cauchy-sequence-Metric-Space
          ( metric-space-Complete-Metric-Space M)
          ( cx))
        ( λ μx →
          has-limit-modulated-cauchy-sequence-Complete-Metric-Space M (x , μx))
        ( is-cauchy-x)

    lim-cauchy-sequence-Complete-Metric-Space :
      cauchy-sequence-Complete-Metric-Space M → type-Complete-Metric-Space M
    lim-cauchy-sequence-Complete-Metric-Space x =
      pr1 (has-limit-cauchy-sequence-Complete-Metric-Space x)

    is-limit-lim-cauchy-sequence-Complete-Metric-Space :
      (x : cauchy-sequence-Complete-Metric-Space M) →
      is-limit-cauchy-sequence-Metric-Space
        ( metric-space-Complete-Metric-Space M)
        ( x)
        ( lim-cauchy-sequence-Complete-Metric-Space x)
    is-limit-lim-cauchy-sequence-Complete-Metric-Space x =
      pr2 (has-limit-cauchy-sequence-Complete-Metric-Space x)
```

### If every Cauchy sequence has a limit in a metric space, the metric space is complete

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-sequences-have-limits-Metric-Space : UU (l1 ⊔ l2)
  cauchy-sequences-have-limits-Metric-Space =
    (x : cauchy-sequence-Metric-Space M) →
    has-limit-cauchy-sequence-Metric-Space M x

module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (H : cauchy-sequences-have-limits-Metric-Space M)
  where

  is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space :
    is-complete-Metric-Space M
  is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space =
    is-complete-metric-space-modulated-cauchy-sequences-have-limits-Metric-Space
      ( M)
      ( λ (x , μx) → H (x , unit-trunc-Prop μx))

  complete-metric-space-cauchy-sequences-have-limits-Metric-Space :
    Complete-Metric-Space l1 l2
  complete-metric-space-cauchy-sequences-have-limits-Metric-Space =
    ( M ,
      is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space)
```
