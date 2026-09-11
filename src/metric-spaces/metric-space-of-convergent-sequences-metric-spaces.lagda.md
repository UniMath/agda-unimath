# The metric space of convergent sequences in metric spaces

```agda
module metric-spaces.metric-space-of-convergent-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.metric-space-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequences-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

The [convergent sequences](metric-spaces.convergent-sequences-metric-spaces.md)
in a [metric space](metric-spaces.metric-spaces.md) inherit the
[subbspace metric structure](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of sequences](metric-spaces.sequences-metric-spaces.md). This
defines the
{{#concept "metric space of convergent sequences in a metric space" Agda=metric-space-of-convergent-sequences-Metric-Space}}.

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
