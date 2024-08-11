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

Sequences in metric spaces are sequences in the underlyng types.

## Definitions

### Sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l)
  where

  Sequence-Metric-Space : UU l
  Sequence-Metric-Space = sequence (type-Metric-Space M)
```

### Constant sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l) (x : type-Metric-Space M)
  where

  constant-Sequence-Metric-Space : Sequence-Metric-Space M
  constant-Sequence-Metric-Space n = x
```
