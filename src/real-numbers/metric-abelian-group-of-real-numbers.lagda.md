# The metric abelian group of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.metric-abelian-group-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces

open import real-numbers.isometry-addition-real-numbers
open import real-numbers.isometry-negation-real-numbers
open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

The [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) form a
[metric abelian group](analysis.metric-abelian-groups.md) under
[addition](real-numbers.addition-real-numbers.md) with regards to their
[standard metric space](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
metric-ab-ℝ : (l : Level) → Metric-Ab (lsuc l) l
metric-ab-ℝ l =
  ( ab-add-ℝ l ,
    structure-Pseudometric-Space (pseudometric-space-ℝ l) ,
    is-extensional-pseudometric-space-ℝ ,
    is-isometry-neg-ℝ ,
    is-isometry-left-add-ℝ)
```
