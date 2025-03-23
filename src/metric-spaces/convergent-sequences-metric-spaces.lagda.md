# Convergent sequences in metric spaces

```agda
module metric-spaces.convergent-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.limits-sequences-metric-spaces
open import metric-spaces.limits-sequences-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [sequence](metric-spaces.sequences-metric-spaces.md) in a
[metric-space](metric-spaces.metric-spaces.md) is
{{# concept "convergent" Disambiguation="sequence in a metric space" Agda=convergent-sequence-Metric-Space}}
if it has a [limit](metric-spaces.limits-sequences-metric-spaces.md).

Asymptotically indistinguishable convergent sequences in a metric space have the
same limit.

## Definitions

### Existence of limits of sequences in a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-Metric-Space M)
  where

  has-limit-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-sequence-Metric-Space =
    Σ (type-Metric-Space M) (is-limit-sequence-Metric-Space M u)

  limit-has-limit-sequence-Metric-Space :
    has-limit-sequence-Metric-Space → type-Metric-Space M
  limit-has-limit-sequence-Metric-Space H = pr1 H

  is-limit-limit-has-limit-sequence-Metric-Space :
    (H : has-limit-sequence-Metric-Space) →
    is-limit-sequence-Metric-Space M u
      (limit-has-limit-sequence-Metric-Space H)
  is-limit-limit-has-limit-sequence-Metric-Space H = pr2 H
```

### Convergent sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  convergent-sequence-Metric-Space : UU (l1 ⊔ l2)
  convergent-sequence-Metric-Space =
    Σ (sequence-Metric-Space M) (has-limit-sequence-Metric-Space M)

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : convergent-sequence-Metric-Space M)
  where

  seq-convergent-sequence-Metric-Space :
    sequence-Metric-Space M
  seq-convergent-sequence-Metric-Space = pr1 u

  has-limit-convergent-sequence-Metric-Space :
    has-limit-sequence-Metric-Space M seq-convergent-sequence-Metric-Space
  has-limit-convergent-sequence-Metric-Space = pr2 u

  limit-convergent-sequence-Metric-Space : type-Metric-Space M
  limit-convergent-sequence-Metric-Space =
    pr1 has-limit-convergent-sequence-Metric-Space

  is-limit-limit-convergent-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M
      seq-convergent-sequence-Metric-Space
      limit-convergent-sequence-Metric-Space
  is-limit-limit-convergent-sequence-Metric-Space =
    pr2 has-limit-convergent-sequence-Metric-Space
```

### Asymptotically indistinguishable convergent sequences in a metric space have the same limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u v : convergent-sequence-Metric-Space M)
  (H :
    is-asymptotically-indistinguishable-sequence-Metric-Space M
      ( seq-convergent-sequence-Metric-Space M u)
      ( seq-convergent-sequence-Metric-Space M v))
  where

  preserves-limit-asymptotically-indistinguishable-convergent-sequence-Metric-Space :
    limit-convergent-sequence-Metric-Space M u ＝
    limit-convergent-sequence-Metric-Space M v
  preserves-limit-asymptotically-indistinguishable-convergent-sequence-Metric-Space =
    eq-limit-sequence-Metric-Space M
      ( seq-convergent-sequence-Metric-Space M v)
      ( limit-convergent-sequence-Metric-Space M u)
      ( limit-convergent-sequence-Metric-Space M v)
      ( preserves-limit-asymptotically-indistinguishable-sequence-Pseudometric-Space
        ( pseudometric-Metric-Space M)
        ( seq-convergent-sequence-Metric-Space M u)
        ( seq-convergent-sequence-Metric-Space M v)
        ( H)
        ( limit-convergent-sequence-Metric-Space M u)
        ( is-limit-limit-convergent-sequence-Metric-Space M u))
      (is-limit-limit-convergent-sequence-Metric-Space M v)
```
