# The metric space of sequences in a metric space

```agda
module metric-spaces.metric-space-of-sequences-metric-spaces where
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

The type of [sequences](metric-spaces.sequences-metric-spaces.md) in a
[metric space](metric-spaces.metric-spaces.md) itself forms a metric space.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  sequence-Metric-Space : Metric-Space l1 l2
  sequence-Metric-Space = Π-Metric-Space ℕ (λ _ → M)
```
