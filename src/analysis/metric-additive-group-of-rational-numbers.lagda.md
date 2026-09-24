# The metric additive group of rational numbers

```agda
module analysis.metric-additive-group-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
```

</details>

## Idea

The [rational numbers](elementary-number-theory.rational-numbers.md) form a
[metric abelian group](analysis.metric-abelian-groups.md).

## Definition

```agda
metric-ab-add-ℚ : Metric-Ab lzero lzero
metric-ab-add-ℚ =
  ( abelian-group-add-ℚ ,
    pseudometric-structure-ℚ ,
    is-extensional-pseudometric-space-ℚ ,
    is-short-map-neg-ℚ ,
    is-short-map-left-add-ℚ)
```
