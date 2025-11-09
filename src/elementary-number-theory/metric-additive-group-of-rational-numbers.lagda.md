# The metric additive group of rational numbers

```agda
module elementary-number-theory.metric-additive-group-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import elementary-number-theory.additive-group-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
```

</details>

## Idea

[Addition](elementary-number-theory.addition-rational-numbers.md) on the
[rational numbers](elementary-number-theory.rational-numbers.md) forms a
[metric abelian group](analysis.metric-abelian-groups.md).

## Definition

```agda
metric-ab-add-ℚ : Metric-Ab lzero lzero
metric-ab-add-ℚ =
  ( abelian-group-add-ℚ ,
    pseudometric-structure-Metric-Space metric-space-ℚ ,
    is-extensional-pseudometric-space-ℚ ,
    is-isometry-neg-ℚ ,
    is-isometry-add-ℚ)
```
