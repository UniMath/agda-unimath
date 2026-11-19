# Addition of Cauchy real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-cauchy-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups
open import analysis.metric-abelian-groups-metric-quotients-cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-additive-group-of-rational-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.cauchy-real-numbers
```

</details>

## Idea

The [Cauchy real numbers](real-numbers.cauchy-real-numbers.md) inherit a
[metric abelian group structure](analysis.metric-abelian-groups.md) structure
from the
[metric abelian group of the metric quotient of the Cauchy pseudocompletion](analysis.metric-abelian-groups-metric-quotients-cauchy-pseudocompletions-metric-abelian-groups.md)
on the
[metric abelian group of rational numbers](analysis.metric-additive-group-of-rational-numbers.md).

## Definition

```agda
metric-ab-add-cauchy-ℝ : Metric-Ab lzero lzero
metric-ab-add-cauchy-ℝ =
  metric-ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab metric-ab-add-ℚ

ab-add-cauchy-ℝ : Ab lzero
ab-add-cauchy-ℝ = ab-Metric-Ab metric-ab-add-cauchy-ℝ

add-cauchy-ℝ : cauchy-ℝ → cauchy-ℝ → cauchy-ℝ
add-cauchy-ℝ = add-Ab ab-add-cauchy-ℝ

neg-cauchy-ℝ : cauchy-ℝ → cauchy-ℝ
neg-cauchy-ℝ = neg-Ab ab-add-cauchy-ℝ
```

## Properties

### Abelian group properties of addition

```agda
abstract
  associative-add-cauchy-ℝ :
    (x y z : cauchy-ℝ) →
    add-cauchy-ℝ (add-cauchy-ℝ x y) z ＝ add-cauchy-ℝ x (add-cauchy-ℝ y z)
  associative-add-cauchy-ℝ = associative-add-Ab ab-add-cauchy-ℝ

  left-unit-law-add-cauchy-ℝ :
    (x : cauchy-ℝ) → add-cauchy-ℝ zero-cauchy-ℝ x ＝ x
  left-unit-law-add-cauchy-ℝ = left-unit-law-add-Ab ab-add-cauchy-ℝ

  right-unit-law-add-cauchy-ℝ :
    (x : cauchy-ℝ) → add-cauchy-ℝ x zero-cauchy-ℝ ＝ x
  right-unit-law-add-cauchy-ℝ = right-unit-law-add-Ab ab-add-cauchy-ℝ

  left-inverse-law-add-cauchy-ℝ :
    (x : cauchy-ℝ) → add-cauchy-ℝ (neg-cauchy-ℝ x) x ＝ zero-cauchy-ℝ
  left-inverse-law-add-cauchy-ℝ =
    left-inverse-law-add-Ab ab-add-cauchy-ℝ

  right-inverse-law-add-cauchy-ℝ :
    (x : cauchy-ℝ) → add-cauchy-ℝ x (neg-cauchy-ℝ x) ＝ zero-cauchy-ℝ
  right-inverse-law-add-cauchy-ℝ =
    right-inverse-law-add-Ab ab-add-cauchy-ℝ
```
