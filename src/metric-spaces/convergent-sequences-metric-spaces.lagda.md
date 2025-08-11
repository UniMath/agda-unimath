# Convergent sequences in metric spaces

```agda
module metric-spaces.convergent-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.limits-of-sequences-premetric-spaces
open import metric-spaces.limits-of-sequences-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A [sequence](metric-spaces.sequences-metric-spaces.md) in a
[metric space](metric-spaces.metric-spaces.md) is
{{#concept "convergent" Disambiguation="sequence in a metric space" Agda=convergent-sequence-Metric-Space}}
if it has a [limit](metric-spaces.limits-of-sequences-metric-spaces.md).
[Short maps](metric-spaces.short-functions-metric-spaces.md) between metric
spaces preserve convergent sequences.

## Definitions

### Convergent sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  subtype-convergent-sequence-Metric-Space :
    subtype (l1 ⊔ l2) (sequence-type-Metric-Space M)
  subtype-convergent-sequence-Metric-Space =
    has-limit-prop-sequence-Metric-Space M

  convergent-sequence-Metric-Space : UU (l1 ⊔ l2)
  convergent-sequence-Metric-Space =
    type-subtype subtype-convergent-sequence-Metric-Space

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : convergent-sequence-Metric-Space M)
  where

  seq-convergent-sequence-Metric-Space : sequence-type-Metric-Space M
  seq-convergent-sequence-Metric-Space = pr1 u

  has-limit-convergent-sequence-Metric-Space :
    has-limit-sequence-Metric-Space M seq-convergent-sequence-Metric-Space
  has-limit-convergent-sequence-Metric-Space = pr2 u

  limit-convergent-sequence-Metric-Space : type-Metric-Space M
  limit-convergent-sequence-Metric-Space =
    limit-has-limit-sequence-Metric-Space M
      seq-convergent-sequence-Metric-Space
      has-limit-convergent-sequence-Metric-Space

  is-limit-limit-convergent-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M
      seq-convergent-sequence-Metric-Space
      limit-convergent-sequence-Metric-Space
  is-limit-limit-convergent-sequence-Metric-Space =
    is-limit-limit-has-limit-sequence-Metric-Space M
      seq-convergent-sequence-Metric-Space
      has-limit-convergent-sequence-Metric-Space
```

## Properties

### Short maps between metric spaces preserve convergent sequences and their limits

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  (u : convergent-sequence-Metric-Space A)
  where

  seq-short-map-convergent-sequence-Metric-Space : sequence-type-Metric-Space B
  seq-short-map-convergent-sequence-Metric-Space =
    map-sequence
      ( map-short-function-Metric-Space A B f)
      ( seq-convergent-sequence-Metric-Space A u)

  has-limit-seq-short-map-convergent-sequence-Metric-Space :
    has-limit-sequence-Metric-Space B
      seq-short-map-convergent-sequence-Metric-Space
  has-limit-seq-short-map-convergent-sequence-Metric-Space =
    ( map-short-function-Metric-Space A B f
      ( limit-convergent-sequence-Metric-Space A u)) ,
    ( short-map-limit-sequence-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)
      ( seq-convergent-sequence-Metric-Space A u)
      ( limit-convergent-sequence-Metric-Space A u)
      ( is-limit-limit-convergent-sequence-Metric-Space A u))

  map-short-map-convergent-sequence-Metric-Space :
    convergent-sequence-Metric-Space B
  map-short-map-convergent-sequence-Metric-Space =
    seq-short-map-convergent-sequence-Metric-Space ,
    has-limit-seq-short-map-convergent-sequence-Metric-Space

  eq-limit-short-map-convergent-sequence-Metric-Space :
    ( map-short-function-Metric-Space A B f
      ( limit-convergent-sequence-Metric-Space A u)) ＝
    ( limit-convergent-sequence-Metric-Space B
      ( map-short-map-convergent-sequence-Metric-Space))
  eq-limit-short-map-convergent-sequence-Metric-Space = refl
```

## See also

- The
  [metric space of convergent sequences](metric-spaces.metric-space-of-convergent-sequences-metric-spaces.md)
  in a metric space
