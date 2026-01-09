# The action on convergent sequences of short maps between metric spaces

```agda
module metric-spaces.action-on-convergent-sequences-short-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

The composition of a [short map](metric-spaces.short-maps-metric-spaces.md)
between [metric spaces](metric-spaces.metric-spaces.md) and a
[convergent sequence](metric-spaces.convergent-sequences-metric-spaces.md) is a
convergent sequence.

## Properties

### Short maps between metric spaces preserve convergent sequences and their limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-map-Metric-Space A B)
  (u : convergent-sequence-Metric-Space A)
  where

  sequence-map-convergent-sequence-short-map-Metric-Space :
    sequence-type-Metric-Space B
  sequence-map-convergent-sequence-short-map-Metric-Space =
    map-sequence
      ( map-short-map-Metric-Space A B f)
      ( seq-convergent-sequence-Metric-Space A u)

  limit-map-convergent-sequence-short-map-Metric-Space :
    type-Metric-Space B
  limit-map-convergent-sequence-short-map-Metric-Space =
    map-short-map-Metric-Space A B f
      ( limit-convergent-sequence-Metric-Space A u)

  is-limit-limit-map-convergent-sequence-short-map-Metric-Space :
    is-limit-sequence-Metric-Space B
      ( sequence-map-convergent-sequence-short-map-Metric-Space)
      ( limit-map-convergent-sequence-short-map-Metric-Space)
  is-limit-limit-map-convergent-sequence-short-map-Metric-Space =
    preserves-limits-sequence-short-map-Metric-Space A B f
      ( seq-convergent-sequence-Metric-Space A u)
      ( limit-convergent-sequence-Metric-Space A u)
      ( is-limit-limit-convergent-sequence-Metric-Space A u)

  has-limit-sequence-map-convergent-sequence-short-map-Metric-Space :
    has-limit-sequence-Metric-Space B
      sequence-map-convergent-sequence-short-map-Metric-Space
  has-limit-sequence-map-convergent-sequence-short-map-Metric-Space =
    ( limit-map-convergent-sequence-short-map-Metric-Space ,
      is-limit-limit-map-convergent-sequence-short-map-Metric-Space)

  map-convergent-sequence-short-map-Metric-Space :
    convergent-sequence-Metric-Space B
  map-convergent-sequence-short-map-Metric-Space =
    sequence-map-convergent-sequence-short-map-Metric-Space ,
    has-limit-sequence-map-convergent-sequence-short-map-Metric-Space

  eq-limit-short-map-convergent-sequence-Metric-Space :
    map-short-map-Metric-Space A B f
      ( limit-convergent-sequence-Metric-Space A u) ＝
    limit-convergent-sequence-Metric-Space B
      ( map-convergent-sequence-short-map-Metric-Space)
  eq-limit-short-map-convergent-sequence-Metric-Space = refl
```
