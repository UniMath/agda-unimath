# Sequences in metric spaces

```agda
module metric-spaces.sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.metric-spaces
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a metric space" Agda=sequence-Metric-Space}}
in a [metric space](metric-spaces.metricc-spaces.md) is a sequence in its
underlying type.

## Definitions

### Sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  sequence-Metric-Space : UU l1
  sequence-Metric-Space = sequence (type-Metric-Space M)
```
