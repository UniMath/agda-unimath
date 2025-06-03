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

A
{{#concept "sequence" Disambiguation="in a metric space" Agda=sequence-type-Metric-Space}}
in a [metric space](metric-spaces.metric-spaces.md) is a
[sequence](lists.sequences.md) in its underlying type.

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
