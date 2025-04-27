# The metric space of convergent sequences in metric spaces

```agda
module metric-spaces.metric-space-of-convergent-sequences-in-a-metric-space where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The
[convergent sequences in a metric space](metric-spaces.convergent-sequences-metric-spaces.md)
inherits the
[subbspace metric structure](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of sequences](metrics-spaced.sequences-metric-spaces.md). It is
the
{{#concept "metric space of convergent sequences in a metric space" Agda=metric-space-of-convergent-sequences-Metric-Space}}

## Definitions

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  metric-space-of-convergent-sequences-Metric-Space : Metric-Space (l1 ⊔ l2) l2
  metric-space-of-convergent-sequences-Metric-Space =
    subspace-Metric-Space
      ( sequence-Metric-Space M)
      ( subtype-convergent-sequence-Metric-Space M)
```
