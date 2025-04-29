# Sequences in metric spaces

```agda
module metric-spaces.sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The type of [sequences](foundation.sequences.md) in a
[metric space](metric-spaces.metric-spaces.md) inherits the
[product metric structure](metric-spaces.dependent-products-metric-spaces.md).
This defines the
{{#concept "metric space of sequences" Disambiguation="in a metric space" Agda=sequence-Metric-Space}}
in a metric space.

## Definitions

### The metric space of sequences in a metric space

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  sequence-Metric-Space : Metric-Space l1 l2
  sequence-Metric-Space = Π-Metric-Space ℕ (λ _ → M)

  sequence-type-Metric-Space : UU l1
  sequence-type-Metric-Space =
    type-Metric-Space sequence-Metric-Space
```
