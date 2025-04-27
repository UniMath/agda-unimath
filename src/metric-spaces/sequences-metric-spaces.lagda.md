# Sequences in metric spaces

```agda
module metric-spaces.sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.sequences
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.sequences-premetric-spaces
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a metric space" Agda=sequence-type-Metric-Space}}
in a [metric space](metric-spaces.metric-spaces.md) is a
[sequence in its underlying pseudometric space](metric-spaces.sequences-pseudometric-spaces.md):
a [sequence](foundation.sequences.md) in its underlying type.

## Definitions

### Sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  sequence-type-Metric-Space : UU l1
  sequence-type-Metric-Space =
    sequence-type-Premetric-Space (premetric-Metric-Space M)
```
