# Totally bounded proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.totally-bounded-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.totally-bounded-metric-spaces

open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.totally-bounded-subsets-real-numbers
open import real-numbers.unit-closed-interval-real-numbers
open import real-numbers.unit-linear-interpolation-proper-closed-intervals-real-numbers
```

</details>

## Idea

Any
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
is [totally bounded](real-numbers.totally-bounded-subsets-real-numbers.md).

## Proposition

### Every proper closed interval in `ℝ` is totally bounded

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I : proper-closed-interval-ℝ l1 l2)
  where abstract

  is-totally-bounded-proper-closed-interval-ℝ :
    is-totally-bounded-subset-ℝ
      ( lsuc (l1 ⊔ l2 ⊔ l))
      ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
  is-totally-bounded-proper-closed-interval-ℝ =
    preserves-is-totally-bounded-uniform-homeo-Metric-Space
      ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l))
      ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
      ( uniform-homeo-unit-linear-interpolation-proper-closed-interval-ℝ l I)
      ( is-totally-bounded-unit-closed-interval-ℝ (l1 ⊔ l2 ⊔ l))
```

## Definition

### The inhabited totally bounded metric space induced by a closed real interval

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I : proper-closed-interval-ℝ l1 l2)
  where

  inhabited-totally-bounded-subset-proper-closed-interval-ℝ :
    inhabited-totally-bounded-subset-ℝ
      ( l1 ⊔ l2 ⊔ l)
      ( l1 ⊔ l2 ⊔ l)
      ( lsuc (l1 ⊔ l2 ⊔ l))
  pr1 inhabited-totally-bounded-subset-proper-closed-interval-ℝ =
    ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I ,
      is-totally-bounded-proper-closed-interval-ℝ l I)
  pr2 inhabited-totally-bounded-subset-proper-closed-interval-ℝ =
    is-inhabited-subtype-proper-closed-interval-ℝ (l2 ⊔ l) I
```
