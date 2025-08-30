# Totally bounded subsets of the real numbers

```agda
module real-numbers.totally-bounded-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels
open import metric-spaces.totally-bounded-metric-spaces
open import foundation.dependent-pair-types
open import metric-spaces.subspaces-metric-spaces
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.dedekind-real-numbers
open import foundation.subtypes
open import real-numbers.subsets-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
```

</details>

## Idea

A [subset of the real numbers](real-numbers.subsets-real-numbers.md) is
{{#concept "totally bounded" disambiguation="subset of the real numbers" WDID=Q1362228 WD="totally bounded space" Agda=is-totally-bounded-subset-ℝ}}
if it is [totally bounded](metric-spaces.totally-bounded-metric-spaces.md) as
a [subspace](metric-spaces.subspaces-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level} (S : subset-ℝ l1 l2)
  where

  is-totally-bounded-prop-subset-ℝ : Prop (lsuc l1 ⊔ lsuc (lsuc l2))
  is-totally-bounded-prop-subset-ℝ =
    is-totally-bounded-prop-Metric-Space
      ( subspace-Metric-Space (metric-space-ℝ l2) S)

  is-totally-bounded-subset-ℝ : UU (lsuc l1 ⊔ lsuc (lsuc l2))
  is-totally-bounded-subset-ℝ = type-Prop is-totally-bounded-prop-subset-ℝ

totally-bounded-subset-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc (lsuc l2))
totally-bounded-subset-ℝ l1 l2 =
  type-subtype (is-totally-bounded-prop-subset-ℝ {l1} {l2})

module _
  {l1 l2 : Level} (S : totally-bounded-subset-ℝ l1 l2)
  where

  subset-totally-bounded-subset-ℝ : subset-ℝ l1 l2
  subset-totally-bounded-subset-ℝ = pr1 S

  is-totally-bounded-totally-bounded-subset-ℝ :
    is-totally-bounded-subset-ℝ subset-totally-bounded-subset-ℝ
  is-totally-bounded-totally-bounded-subset-ℝ = pr2 S
```

## Properties

### Totally bounded subsets of `ℝ` have a supremum

```agda
abstract

```
