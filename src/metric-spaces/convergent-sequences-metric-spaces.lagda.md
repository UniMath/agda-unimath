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
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [sequence](metric-spaces.sequences-metric-spaces.md) in a
[metric-space](metric-spaces.metric-spaces.md) is
{{# concept "convergent" Disambiguation="sequence in a metric space" Agda=convergent-sequence-Metric-Space}}
if it has a [limit](metric-spaces.limits-sequences-metric-spaces.md).

## Definitions

### The property of having a limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (u : sequence-Metric-Space M)
  where

  has-limit-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-sequence-Metric-Space =
    Σ (type-Metric-Space M) (is-limit-sequence-Metric-Space M u)
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

  sequence-convergent-sequence-Metric-Space :
    sequence-Metric-Space M
  sequence-convergent-sequence-Metric-Space = pr1 u

  has-limit-convergent-sequence-Metric-Space :
    has-limit-sequence-Metric-Space M sequence-convergent-sequence-Metric-Space
  has-limit-convergent-sequence-Metric-Space = pr2 u

  limit-convergent-sequence-Metric-Space : type-Metric-Space M
  limit-convergent-sequence-Metric-Space =
    pr1 has-limit-convergent-sequence-Metric-Space

  is-limit-convergent-sequence-Metric-Space :
    is-limit-sequence-Metric-Space M
      sequence-convergent-sequence-Metric-Space
      limit-convergent-sequence-Metric-Space
  is-limit-convergent-sequence-Metric-Space =
    pr2 has-limit-convergent-sequence-Metric-Space
```
