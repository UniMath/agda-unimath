# Shifts of sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.shifts-sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.sequential-diagrams-isometries-metric-spaces
```

</details>

## Idea

The
{{#concept "shift" Disambiguation="of a sequential diagram of isometries" Agda=shift-sequential-diagram-isometry-Metric-Space}}
of a
[sequential diagram](metric-spaces.sequential-diagrams-isometries-metric-spaces.md)
of [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md)

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

is the sequential diagram

```text
     f₁       f₂       f₃
 M₁ ----> M₂ ----> M₃ ----> ⋯
```

## Definitions

### Shifts of sequential diagrams of isometries

```agda
module _
  {l1 l2 : Level}
  (M : sequential-diagram-isometry-Metric-Space l1 l2)
  where

  shift-sequential-diagram-isometry-Metric-Space :
    sequential-diagram-isometry-Metric-Space l1 l2
  pr1 shift-sequential-diagram-isometry-Metric-Space n =
    seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ n)
  pr2 shift-sequential-diagram-isometry-Metric-Space n =
    seq-isometry-sequential-diagram-isometry-Metric-Space M (succ-ℕ n)
```
